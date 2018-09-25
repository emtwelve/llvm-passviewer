#!/usr/bin/env python

from __future__ import print_function, division
from functools import reduce
try: from past.builtins import xrange
except ImportError as err:
    from sys import version_info
    if version_info[0] != 2: raise err

import re
import difflib
from glob import glob
from errno import EEXIST
from sys import argv, exit, stdout
from argparse import ArgumentParser
from collections import defaultdict, Counter
from os import makedirs, remove, listdir, devnull
from os.path import join, isfile, basename, split as pathsplit

MAIN_OUTPUT_DIR = "pv_output"
LOCAL_OUTPUT_DIR = None # To be determined once we get the -print-after-all file

# TODO: clean up css strings
light_diff_style_css = """
<style>
body {
    background-color:cornsilk
}
a {
    font-family:monospace;
}
table {
    font-family:monospace;
    border: 3px solid black;
    color:black;
    background-color:white;
    overflow:auto;
    border-collapse:collapse; // remove gaps in rows
    border-spacing: 0;
}
table th {
    border: 3px solid black;
}
table td {
    font-size: 12px;
}
.passtitle {
    font-family:monospace;
}
.diff_header {
    background-color:orange;
}
td.diff_header {
    text-align:right;
}
.diff_next {
    background-color:darkorchid;
}
.diff_add {
    background-color:aquamarine; //chartreuse
}
.diff_sub {
    background-color:mistyrose;
}
.diff_chg {
    background-color:cyan;
}
.constant {
    color:orange;
}
.llvm_keyword {
    color:crimson;
}
.localident {
    color:orange;
}
.comment {
    color:gray;
}
.globalident {
    color:fuchsia;
}
.type {
    color:deepskyblue;
}
</style>
"""

dark_diff_style_css = """
<style>
body {
    background-color:darkgray;
}
a {
    font-family:monospace;
}
table {
    font-family:monospace;
    border: 3px solid black;
    color:yellow;
    background-color:black;
    border-collapse:collapse; // remove gaps in rows
}
table th {
    border: 3px solid black;
}
table td {
    font-size: 12px;
}
.passtitle {
    font-family:monospace;
}
.diff_header {
    background-color:firebrick;
}
td.diff_header {
    text-align:right;
}
.diff_next {
    background-color:darkorchid;
}
.diff_add {
    background-color:green;
}
.diff_sub {
    background-color:maroon;
}
.diff_chg {
    background-color:darkslateblue;
}
.constant {
    color:orange;
}
.llvm_keyword {
    color:crimson;
}
.localident {
    color:orange;
}
.comment {
    color:gray;
}
.globalident {
    color:fuchsia;
}
.type {
    color:deepskyblue;
}
</style>
"""

##################################################
### HTML generation helpers
##################################################
# TODO: see if standard library has HTML helpers
def h2(s): return "<h2>" + s + "</h2><br/>\n" # row
def tr(s): return "<tr>" + s + "</tr>\n" # row
def td(s): return "<td>" + s + "</td>" # col
def th(s): return "<th>" + s + "</th>\n" # header
def a(s, link): return '<a href="'+link+'"> ' + s + ' </a>\n'
def span(s, classname): return '<span class="'+classname+'"> ' + s + ' </span>'
def table(s): return "<table>" + s + "</table>\n"
def body(s): return "<body>" + s + "</body>\n"
def title(s): return "<title>" + s + "</title>\n"
def html(s): return "<html>" + s + "</html>\n"
def cat(*strs): return reduce(lambda x,y: x+y, strs)

##################################################
### Utility functions
##################################################
PASS_DELIMITER = "\n\nPASS_DELIMITER_9b_cf_d0_50_f3_fb_35_5f_63_ae\n\n"
class RegexEnum():
    def __init__(self): self.x = -1
    def incr(self, matchObj): self.x += 1; return 2*PASS_DELIMITER + str(self.x) + matchObj.expand(r"\1")

class Pass():
    def __init__(s, regex_match):
        s.pass_num  = int(regex_match.get('pass_num', ""))
        s.pass_name = regex_match.get('pass_name', "")
        s.pass_type = regex_match.get('pass_type', "")
        s.obj_name  = regex_match.get('obj_name', "")
        s.pass_body = regex_match.get('pass_body', "")
        s.next = None
        s.prev = None
        s.mod_prevs = {}
        s.mod_nexts = {}
        s.ir_file_path = None
    def __repr__(self):
        return str(self.pass_num) + self.pass_name + self.obj_name
    def __str__(self):
        s = "0"*(4-len(str(self.pass_num))) + str(self.pass_num)
        s += " "*(4-len(s)) + ": "
        s += " "*(5-len(s)) + self.pass_name
        s += " "*(60-len(s)) + " ---- "
        s += " "*(65-len(s)) + self.pass_type
        s += " "*(70-len(s)) + self.obj_name
        return s

def printRefl(obj):
  for field in dir(obj):
    res = eval('obj.'+field)
    print(field, end=':\t')
    print(str(res)[:50])

def get_unique_names(listOfPassObjects):
    return list(set(map(lambda x: x.obj_name, listOfPassObjects)))

def print_unique_names(listOfPassObjects):
    for name in get_unique_names(listOfPassObjects):
        qlog(name,"\n")

def slugify(s):
    return re.sub('[-\s]+', '-', re.sub('[^\w\s-]', '', s).strip().lower())

def get_path_leaf(path):
    head, tail = pathsplit(path)
    return tail or basename(head)

def getPasses(pattern, string):
    passProlog = PASS_DELIMITER + r"(?P<pass_num>\d+)\n?.*?After (?P<pass_name>[\w\s'\-()<>%$#!:/&]*?)(?:\*\*\*|:)"
    passEpilog = r"(?P<pass_body>(?:.|\n)*?)" + PASS_DELIMITER
    list_of_dictionaries = finditerlistdict(passProlog + pattern + passEpilog, string)
    list_of_objects = map(lambda regm_dict: Pass(regm_dict), list_of_dictionaries)
    return list(list_of_objects)

def finditerlistdict(pattern, string, flags=0):
    return map(lambda match_obj: match_obj.groupdict(),
               list(re.finditer(pattern, string, flags)))

def makedir(name):
    try:
        makedirs(name)
    except OSError as e:
        if e.errno == EEXIST and name != MAIN_OUTPUT_DIR:
            if not args.overwrite:
                return
            else:
                qlog(name, "already exists")
            raise

def owcfunction(functionName, name, s):
    return owclocal(join(slugify(functionName), name), s)
def owclocal(name, s):
    return owccur(join(LOCAL_OUTPUT_DIR, name), s)
def owcglobal(name, s):
    return owccur(join(MAIN_OUTPUT_DIR, name), s)
def owccur(name, s):
    plfd = open(name, 'w') # binary mode. in particular, so \r\n does not replace \n
    plfd.write(s)
    plfd.close()
    vlog("Generated " + name)
    return name

def qlog(*args): # printing anytime (except when explicitly told to be quiet)
    if not QUIET:
        for arg in args:
            print(arg, end=' ')

def vlog(*args): # verbose printing
    if VERBOSE:
        for arg in args:
            print(arg, end='')
        print()

def display_loader(iteration, limit):
    """ Displays loading progress ^.^ """
    percent = (float(iteration) / limit)*100
    dashes = int(percent / 2.)
    display_value = min(int(round(percent))+1,100)
    qlog("[" + "-"*dashes + " "*(49-dashes) + "] " + str(display_value) + "%\r")
    stdout.flush()
    if iteration >= limit-1:
        qlog("\n")

##################################################
### Main helper functions
##################################################

def AreAllPassesFound(allCPasses, numSubs):
    for i in range(numSubs):
        if i >= len(allCPasses):
            qlog("Some latter passes are missing:\n  ",
                 len(allCPasses), "were found;", numSubs, "should be found\n")
            return False
        passNum = allCPasses[i].pass_num
        if i != passNum:
            qlog("Pass", i, "is not found", allCPasses[i], "\n")
            return False
    return True
#END:AreAllPassesFound

def createPassListingFile(fname, allCPasses):
    allCPassesStr = ""
    for cpass in allCPasses:
        allCPassesStr += str(cpass) + "\n"
    owclocal('listingpasses.'+fname+'.txt', allCPassesStr + str(len(allCPasses)) + " total passes")
    return
#END:createPassListingFile

def listFunctionNames(functionNamesList):
    # If we are missing the function name, list the functions and exit:
    if args.listfns:
        qlog("Listing functions:")
        l = len(functionNamesList)
        for i in xrange(l):
            qlog(functionNamesList[i] + ", ")
            if i % 3 == 2 or i == l-1: qlog("\n") # 3 fns listed per line
        qlog("Exiting\n")
        exit(0)
#END:listFunctionNames

def AddPassType(*pass_groups):
    """ Append the specified pass_type to then end of each entry's n-tuple; destructively """
    def typeAdd(pass_type,pass_group):
        for i in xrange(len(pass_group)):
            pass_group[i].pass_type = pass_type
    map(lambda pair: typeAdd(*pair), pass_groups)
#END:AddPassType

def createFunctionToModuleMap(modules):
    """ Create a functionName -> { set of modules pass objects I belong to } map
        e.g. getRemainder -> { module_object0, module_object1 } """
    fnToModule = defaultdict(set)
    for cpass in modules:
        moduleIR = cpass.pass_body
        for fnName in re.findall(r"\ndefine .*? @(.*?)\(", moduleIR):
            fnToModule[fnName].add(cpass)
    return fnToModule
#END:createFunctionToModuleMap

def createPassNumberToModuleMap(cpasses):
  """ Create a passNumber -> Module-CPass-I-belong-to map """
  numToModule = {}
  for cpass in cpasses:
    if cpass.pass_type == 'M' or cpass.pass_num == 0:
      numToModule[cpass.pass_num] = cpass
    else:
      if cpass.pass_num-1 not in numToModule:
        qlog(cpass)
        qlog(numToModule)
      numToModule[cpass.pass_num] = numToModule[cpass.pass_num-1]
  return numToModule
#END:createPassNumberToModuleMap



def createBasicBlockToFunctionMap(functions):
    bbToFn = defaultdict(set)
    for cpass in functions:
        fnIR = cpass.pass_body
        for bbName in re.findall(r"\n(.*?):\s*;", fnIR): # NOTE: semi-colon only occurs when BB has preds
            bbToFn[bbName].add(cpass)
    return bbToFn

def generateMainPage():
    def h2(s): return "<h2>" + s + "</h2>\n" # row
    mainpageFilename = "index.html"
    html = ""

    # For each local directory (generated from multiple runs of passviewer), list it and
    # generate a link to it's index file:
    for local_output_dir in glob(join(MAIN_OUTPUT_DIR,"*")):
        basename = get_path_leaf(local_output_dir)
        if basename != mainpageFilename: # don't add self to this listing
            html += '<a href="' + basename + '/index.html"> ' + basename + ' </a><br/>\n'

    # Output the mainpage file:
    owcglobal(mainpageFilename, html)
#END:generateMainPage

# TODO
# Make directory for each module:
#                   for each function:
#                      for each basic block:
# in order to seperate what gets diff'd
#
#
# To resolve parent conflicts (when an object is determined to have multiple
#   parents because the parent's have an object of the same name),
#   just generate the .ll file within the
#   directory hierarchy, the previous most parent-pass will (most likely)
#   be the parent of the current object
#
#
# Remove --cmp flag?  Regardless, add so that if two .ll failes are added,
#   they will be compared
#

def generateIRFiles(passesToGenerateFor, fnToModule, bbToFunction):
    def GetFileNameHelper(cpass):
        """ Filename will be of the form: 0000passName.ll """
        pad_i = "0"*(4-len(str(cpass.pass_num))) + str(cpass.pass_num)
        return slugify(pad_i+cpass.pass_name) + ".ll"
    def genIRFile(cpass):
        """ Generate a .ll file in current function's directory """
        filenameGenerated = owcfunction("ir", GetFileNameHelper(cpass), cpass.pass_body)
        cpass.ir_file_path = filenameGenerated
    makedir(join(LOCAL_OUTPUT_DIR,"ir"))
    numPasses = len(passesToGenerateFor)
    for i in xrange(numPasses):
        cpass = passesToGenerateFor[i]
        genIRFile(cpass)
        display_loader(i, numPasses)
#END:generateIRFiles

def generateIndexHTML(filesList, allCPasses):
  def tablecreate(lst):
    return "" if lst==[] else \
      table(tr(th("Num") + th("Pass") + th("Type") + th("Function") + th("Link")) + \
        reduce(lambda x,y: x+y,
               map(lambda cpass:
                   tr(td(str(cpass.pass_num)) + \
                      td(cpass.pass_name) + \
                      td(cpass.pass_type) + \
                      td(cpass.obj_name) + \
                      td(a("diff", slugify(cpass.obj_name) + "/" +              \
                           get_path_leaf(cpass.ir_file_path) + ".html")         \
                           if cpass.pass_type == "F" else                       \
                             a("ir", "ir/" + get_path_leaf(cpass.ir_file_path)) \
                           if cpass.ir_file_path != None else "")), lst)))
  html_str = cat("<!DOCTYPE html>",
    html(cat(title("Compiler Passes"),
      cat(body(cat(h2(COMPILER_INFO),
        a("Back to main", "../index.html"),
        table(tr(td(tablecreate(allCPasses))))))))))
  #html += td('<iframe src="index.html" height="400" width="800"></iframe>')
  owclocal("index.html", html_str)
  # Regenerate the main page in response to creating this new subpage:
  generateMainPage()
#END:generateIndexHTML

def generateDiffs(allCPasses, numToModule, diff_style_css):
    """ This function generates the diff files for all passes by comparing
        the current pass with its previous pass that ran on a common
        module, function, or basic block.
        TODO: add documentation and cleanup: exposed HTML,
              duplicate code, ..."""

    num_passes = len(allCPasses)
    for i in xrange(num_passes):
        cpass = allCPasses[i]
        # cpass object fields:
        #   ir_file_path, mod_nexts, mod_prevs, next, obj_name, pass_body,
        #   pass_name, pass_num, pass_type, prev
        pass_name = cpass.pass_name
        obj_name = cpass.obj_name
        pass_num = str(cpass.pass_num)
        mod_name = numToModule[cpass.pass_num].obj_name
        page_info = "\n<br/>" + \
                    span("Module: " + mod_name, "passtitle") + "\n<br/>" + \
                    span("Pass: " + pass_name, "passtitle") + "\n<br/>" + \
                    span("Object: " + obj_name, "passtitle") + "\n<br/>" + \
                    span("Number: " + pass_num, "passtitle") + "\n<br/>"
        if cpass.pass_type == "F":
            prevpass = cpass.prev
            nextpass = cpass.next

            outputDir = join(LOCAL_OUTPUT_DIR, slugify(cpass.obj_name))

            file0 = prevpass.ir_file_path if prevpass != None else devnull
            file1 = cpass.ir_file_path
            file2 = nextpass.ir_file_path if nextpass != None else None

            table = htmlDiffWrapper(file0, file1)

            home = a('Home', '../index.html')
            prv = '&nbsp;' + a('Prev', '../../../' + join(outputDir, get_path_leaf(file0) + '.html')) if file0 != devnull else ''
            nxt = '&nbsp;' + a('Next', '../../../' + join(outputDir, get_path_leaf(file2) + '.html')) if file2 != None else ''
            page_name = '&nbsp;' + span(file1, "passtitle")
            page_contents = diff_style_css + body(home + prv + nxt + page_name + page_info + table)
            owccur(join(outputDir, get_path_leaf(file1)+'.html'), page_contents)

        elif cpass.pass_type == "M":
            for fn in cpass.mod_prevs:
                fnprev = cpass.mod_prevs.get(fn, None)
                fnnext = cpass.mod_nexts.get(fn, None)

                outputDir = join(LOCAL_OUTPUT_DIR, slugify(fn))

                file0 = fnprev.ir_file_path if fnprev != None else devnull
                file1 = cpass.ir_file_path
                file2 = fnnext.ir_file_path if fnnext != None else None

                table = htmlDiffWrapper(file0, file1)

                home = a('Home', '../index.html')
                prv = '&nbsp;' + a('Prev', '../../../' + join(outputDir, get_path_leaf(file0) + '.html')) if file0 != devnull else ''
                nxt = '&nbsp;' + a('Next', '../../../' + join(outputDir, get_path_leaf(file2) + '.html')) if file2 != None else ''
                page_name = '&nbsp;' + span(file1, "passtitle")
                page_contents = diff_style_css + body(home + prv + nxt + page_name + page_info + table)
                owccur(join(outputDir, get_path_leaf(file1)+'.html'), page_contents)

        display_loader(i, num_passes)
#END:generateDiffs

def htmlTableSemiTranspose(table):
    """ partial table transpose: table is transformed into two tables, one containing each side of diff;
        this allows for better highlighting and scrolling """

    # Modify the table thead
    table = re.sub(r"<thead><tr>(?:<th .*?>.*?</th>)(?P<filename1><th .*?>.*?</th>)(?:<th .*?>.*?</th>)(?P<filename2><th .*?>.*?</th>)</tr></thead>",
                   r"<thead><tr>\g<filename1>\g<filename2></tr></thead>",
                table, flags=re.DOTALL)

    # Modify the table tbody
    match_cols = r"(<tr>)(?P<first3cols>(?:<td .*?>.*?</td>){3})(?P<last3cols>(?:<td .*?>.*?</td>){3})(</tr>)" # for each table row in HTML, get last 3 cols
    lastmatches = map(lambda match: match['last3cols'], finditerlistdict(match_cols, table))
    lastmatches = map(lambda s: '<tr height="16px;padding:0;margin:0;border:0;">' + s + '</tr>\n', lastmatches)
    #lastmatches = map(lambda s: s + '<br/>\n', lastmatches)

    firstmatches = map(lambda match: match['first3cols'], finditerlistdict(match_cols, table))
    firstmatches = map(lambda s: '<tr height="16px;padding:0;margin:0;border:0;">' + s + '</tr>\n', firstmatches)

    table, num = re.subn(match_cols, r"\1\4", table) # remove the columns
    assert num == len(list(lastmatches)) and num == len(list(firstmatches))

    # Add a scrollable single-row columns for both the left diff and right diff; place table within each row
    table = re.sub(r"<tbody>(.*?)</tbody>",
                    '<tbody><tr><td style="overflow-x:scroll;max-width:750px;"><table>' + ''.join(firstmatches) +
                    '</table></td><td></td><td style="overflow-x:scroll;max-width:750px;"><table>' + ''.join(lastmatches) +
                    "</table></td></tr></tbody>",
                    table, flags=re.DOTALL)

    return table
#END:htmlTableSemiTranspose

def htmlDiffWrapper(file0, file1):
    html_diff = difflib.HtmlDiff() if not args.rowsep else difflib.HtmlDiff(wrapcolumn=120)
    try:
      with open(file0, 'r') as fd0:
        with open(file1, 'r') as fd1:
          table = html_diff.make_table(fd0.readlines(), fd1.readlines(), fromdesc=file0, todesc=file1)
    except IOError as error:
        return "\nNo diff created: " + str(error)

    if not args.rowsep:
        table = htmlTableSemiTranspose(table)

    # syntax highlight
    if not args.syntax_off:
        table = ir_html_syntax_highlight(table)

    return table

def ir_html_syntax_highlight(table):
    """ Syntax highlights the input html formatted IR diff """
    prefix = r'(>[^<>]*?)'
    suffix = r'([^<>]*?<)'
    surround = lambda s: prefix + s + suffix # surround so we only modify the text, not HTML tags or attribs
    span_class = lambda s: r'\1<span class="' + s + r'">\2</span>\3' # class for css coloring
    sub = lambda regex,class_name,tbl: re.sub(surround(regex), span_class(class_name), tbl)

    # Preprocess to avoid overlapping matches; between any two spaces
    #   insert idempotent spans:
    table = re.sub(r'&nbsp;(.+?)&nbsp;', r'&nbsp;<span>\1</span>&nbsp;', table)

    # Order matters when highlighting the text
    llvm_keyword = r'(<span>(?:getelementptr|addrspace|extractelement|'+\
                   r'null|align|call|store|load|alloca|br|ret|nounwind|'+\
                   r'inttoptr|ptrtoint|bitcast|addrspacecast|sitofp|'+\
                   r'uitofp|fptosi|fptoui|fpext|fptrunc|sext|zext|trunc|'+\
                   r'atomicrmw|cmpxchg|fence|insertvalue|extractvalue|'+\
                   r'shl|lshr|ashr|and|or|xor|add|fadd|sub|fsub|mul|fmul|'+\
                   r'udiv|fdiv|urem|srem|frem|'+\
                   r'switch|indirectbr|invoke|resume|catchswitch|catchret|'+\
                   r'cleanupret|unreachable|undef|asm|sideeffect|true|false|'+\
                   r'global|constant|external|target|datalayout|triple|'+\
                   r'zeroext|signext|inreg|byval|inalloca|sret|noalias|'+\
                   r'nocapture|nest|returned|nonnull|dereferenceable|'+\
                   r'dereferenceable_or_null|swiftself|swifterror)</span>)'
    constant = r'(?<=&nbsp;)(\d+)'
    localident = r'(%[a-zA-Z_]\w+)'
    globalident = r'(@[\w\.\-"$]+)'
    typ = r'(void|i8|i32|i64|half|float|double|'+\
          r'fp128|x86_fp80|ppc_fp128|x86_mmx|metadata|token|label)'
    #comment = r'(?<=[;])([;].*?)(?:\n)'
    table = sub(llvm_keyword, "llvm_keyword", table)
    table = sub(constant, "constant", table)
    table = sub(localident, "localident", table)
    table = sub(globalident, "globalident", table)
    table = sub(typ, "type", table)
    #table = sub(comment, "comment", table)
    return table
#end:ir_html_syntax_highlight

def generateAcrossChangeDiff(file0, file1, diff_style_css):
    """ TODO: document and cleanup this function """
    global LOCAL_OUTPUT_DIR
    outDir0 = join(MAIN_OUTPUT_DIR, get_path_leaf(file0.replace(".","")))
    outDir1 = join(MAIN_OUTPUT_DIR, get_path_leaf(file1.replace(".","")))
    qlog("Comparing across", file0, "and", file1, "\n",
         "  using the ir files generated in", outDir0, "and", outDir1, "\n")

    LOCAL_OUTPUT_DIR = \
        join(MAIN_OUTPUT_DIR,
             "comparing" + slugify(get_path_leaf(outDir0)) + slugify(get_path_leaf(outDir1)))
    makedir(LOCAL_OUTPUT_DIR)

    makedir(join(LOCAL_OUTPUT_DIR, "acrossdiff"))

    index_html_str = '<a href="../index.html"> Back to main </a><br\>\n'
    outDir0Glob = glob(join(outDir0,join("ir","*.ll")))
    numllFiles = len(outDir0Glob)
    for i in xrange(numllFiles):
        file0 = outDir0Glob[i]
        fileLeaf = get_path_leaf(file0)
        file1 = join(outDir1,join("ir",fileLeaf))

        assert get_path_leaf(file1) in map(lambda x: get_path_leaf(x), glob(join(outDir0, join("ir","*.ll"))))
        assert fileLeaf == get_path_leaf(file1)

        vlog(file0, file1)

        table = htmlDiffWrapper(file0, file1)

        home = '<a href="../index.html"> Home </a>'
        prv = '<a href="' + get_path_leaf(outDir0Glob[i-1]) + '.html"> prev </a>' if i != 0 else ''
        nxt = '<a href="' + get_path_leaf(outDir0Glob[i+1]) + '.html"> next </a>' if i != numllFiles-1 else ''
        page_name = '&nbsp;<span class="passtitle">'+fileLeaf+'</span>'
        owcfunction("acrossdiff",
                    fileLeaf+'.html',
                    diff_style_css + "<body>" + home + prv + nxt + page_name + table + "</body>")

        index_html_str += '<a href="acrossdiff/' + fileLeaf + '.html">' + fileLeaf + '</a><br/>\n'

        display_loader(i, numllFiles)

    owclocal("index.html", index_html_str)
    generateMainPage()
    return
#END:generateAcrossChangeDiff

def handleSingularPAAFile(paa_file, srcFilesList, diff_style_css):
    global LOCAL_OUTPUT_DIR
    global COMPILER_INFO
    LOCAL_OUTPUT_DIR = join(MAIN_OUTPUT_DIR, slugify(get_path_leaf(paa_file)))
    makedir(LOCAL_OUTPUT_DIR)

    passesFile = open(paa_file, 'r')
    passesStr = passesFile.read() + PASS_DELIMITER

    ############
    # Get compiler information occurring before first pass
    COMPILER_INFO = passesStr.split("*** IR Dump After").pop(0) # e.g. compiler name, target, time built, versions (may be empty)

    ############
    # Number all passes and output to file
    passesStr, numSubs = re.subn(r"(\*\*\* IR Dump After|\nAfter )", RegexEnum().incr, passesStr)
    passesStr = COMPILER_INFO + PASS_DELIMITER.join(passesStr.split(PASS_DELIMITER)[1:])

    for srcFile in srcFilesList:
        with open(srcFile, 'r') as fd:
            contents = fd.read()
            passesStr = PASS_DELIMITER + '0000' + contents + PASS_DELIMITER + passesStr

    owclocal('enumd.'+get_path_leaf(paa_file), passesStr)

    ############
    # Find all numbered (i.e. enumd) passes in the LARGE passesStr string:
    qlog("Parsing -print-after-all file", paa_file, "\n")
    nmatch    = r"printing a <null> value"
    ematch    = r" - "
    mmatch    = r"\n?; ModuleID = '(?P<obj_name>.*?)'"
    fmatch    = r"(?:\n+define.*?@|:?\n?# Machine code for function )(?P<obj_name>.*?)(?::|\()"
    dmatch    = r"\ndeclare.*?@(?P<obj_name>.*?)\("
    lmatch    = r"\n(?P<obj_name>[\w\.;<> ]*?):\d*\s*;"

    nullvals  = getPasses(nmatch, passesStr)
    excepts   = getPasses(ematch, passesStr)
    modules   = getPasses(mmatch, passesStr)
    functions = getPasses(fmatch, passesStr)
    declares  = getPasses(dmatch, passesStr)
    natloops  = getPasses(lmatch, passesStr)

    vlog("Finding pass types, sorting, and listing\n")
    ############
    # Add additional pass type information to the regex tuple:
    AddPassType(("N", nullvals), ("E", excepts), ("M", modules), ("F", functions), ("D", declares), ("L", natloops))
    global allCPasses
    # These regexes will find matches of the form:
    allCPasses = excepts + nullvals + declares + modules + functions + natloops
    # Sort all of the passes on pass number (i.e. the order in which the executed):
    allCPasses = sorted(allCPasses, key=lambda match: match.pass_num)

    # Output enumerated passes to a text file:
    createPassListingFile(get_path_leaf(paa_file), allCPasses)
    # Ensure we found all passes; that is, ensure our regex did not miss anything
    assert AreAllPassesFound(allCPasses, numSubs)

    ############
    # Create function to module and basic block to function mapping:
    vlog("Creating hierarchy mappings\n")
    fnToModule = createFunctionToModuleMap(modules)
    bbToFunctn = createBasicBlockToFunctionMap(functions)
    numToModule = createPassNumberToModuleMap(allCPasses)

    def getNextModule(moduleName, allCPasses):
        for cpass in allCPasses:
            if moduleName == cpass.obj_name:
                yield cpass

    def getNextFunction(fnName, modName, numToModule, allCPasses):
      for cpass in allCPasses:
        if   (cpass.pass_type == "F"    and
              cpass.obj_name == fnName and
              numToModule[cpass.pass_num].obj_name == modName):
          yield cpass
        elif (cpass.pass_type == "M" and
              cpass.obj_name == modName):
          assert(numToModule[cpass.pass_num].obj_name == modName)
          yield cpass

    functionNamesList = get_unique_names(functions)
    modulesNamesList = get_unique_names(modules)
    for modName in modulesNamesList:
      for fnName in functionNamesList:
        cpassList = list(getNextFunction(fnName, modName, numToModule, allCPasses))
        for i in xrange(len(cpassList)):
          prev_cpass = cpassList[i-1] if i != 0 else None
          next_cpass = cpassList[i+1] if i != len(cpassList)-1 else None
          if cpassList[i].pass_type == "F":
            cpassList[i].prev = prev_cpass
            cpassList[i].next = next_cpass
          elif cpassList[i].pass_type == "M":
            assert (fnName not in cpassList[i].mod_prevs) and (fnName not in cpassList[i].mod_nexts)
            cpassList[i].mod_prevs[fnName] = prev_cpass
            cpassList[i].mod_nexts[fnName] = next_cpass

    ############
    # List the function names found:
    listFunctionNames(functionNamesList)

    ############
    # Sort the passes to be operated on: TODO: currently only functions, modules, and natloops; add rest
    qlog("Generating IR files in", join(LOCAL_OUTPUT_DIR, join("ir","")), "\n")
    passesToGenerateFor = sorted(functions + modules + natloops, key=lambda cpass: cpass.pass_num)
    generateIRFiles(passesToGenerateFor, fnToModule, bbToFunctn)

    ############
    # Generate main HTML index for pass selecting
    vlog("Generating main HTML index page", join(MAIN_OUTPUT_DIR, "index.html"), "\n")
    match_passNum_passName = r"((\d+)[\w\-]*\.ll)"
    fullFiles = glob(join(join(LOCAL_OUTPUT_DIR,"ir"),'*.ll'))
    matches = map(lambda fullFilename:
                    re.search(match_passNum_passName,
                              get_path_leaf(fullFilename)).groups(),
                  fullFiles)
    generateIndexHTML(matches, allCPasses)

    ############
    # Generate diff files
    qlog("Generating html diffs in", join(LOCAL_OUTPUT_DIR, join("<function_name>","")), "\n")
    for functionName in functionNamesList:
        makedir(join(LOCAL_OUTPUT_DIR, slugify(functionName)))
    generateDiffs(allCPasses, numToModule, diff_style_css)
    qlog("Done\n")
#END: handleSingularPAAFile

##################################################
### Main method TODO: place in function so globals aren't created
##################################################

if __name__ == "__main__":

    ##################
    # Argument handling
    parser = ArgumentParser()
    parser.add_argument("print_after_all_file", help="-print-after-all file from compiler")
    parser.add_argument("-file", help="another from compiler")
    parser.add_argument("-v", "--verbose", action="store_true", help="increase output verbosity")
    parser.add_argument("-q", "--quiet", action="store_true", help="remove any standard output")
    parser.add_argument("-f", "--fn", help="specify function to analyze")
    parser.add_argument("-l", "--listfns", action="store_true", help="list the possible functions to analyze")
    parser.add_argument("-c", type=str, default='dark', choices=['light','dark'], help="color theme")
    parser.add_argument("-s", "--syntax_off", action="store_true", help="turn off syntax highlighting")
    parser.add_argument("-w", "--overwrite", action="store_true", help="avoid overwriting of existing outputs")
    parser.add_argument("-r", "--rowsep", action="store_true", help="change internal HTML layout")
    parser.add_argument("-a", "--asm", nargs='*', help="supply assembly files")
    parser.add_argument("--src", nargs='*', default=[], help="supply source files")

    args = parser.parse_args()
    VERBOSE = args.verbose
    QUIET = args.quiet
    diff_css = dark_diff_style_css if args.c == 'dark' else light_diff_style_css


    makedir(MAIN_OUTPUT_DIR)
    generateMainPage()

    for paa_file in [args.print_after_all_file, args.file]:
        if paa_file:
            handleSingularPAAFile(paa_file, args.src, diff_css)

    if args.file:
        generateAcrossChangeDiff(args.print_after_all_file, args.file, diff_css)

