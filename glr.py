'''

TOPIC: GENERAL LR PARSER
SUBMITTED BY: RAJAT ANJNE(2014UCP1090), AKSHAY NAGAR(2014UCP1524)
SUBMITTED TO: Prof. DINESH GOPLANI
DATE OF SUBMISSION: 08-11-2016


ASSUMPTIONS:
-> Cannot use 'Z' as a non-terminal because used as a start symbol
-> Cannot use '.' and '$' as a terminal because used in Closure and Follow notations
-> Non-terminals can be only Capital letters from A to Y
-> Terminals can be only single characters except '.' and '$'

'''

import re
import traceback
from copy import deepcopy
LEN_TOKEN =3
MAX_NUM_ITEMS=20

#output = 
terms=[]
nonterms=[]
I = []
look_up = []
look_up_red = []
full_table = {}
table = {}
tables=[]
no_term=0
no_nonterm=0
grammar=[]
firstset={}
followset={}
gram_dic = {}
nonterminals=set()
terminals=set()
no_of_line=0
start_symbol = ''

def read_grammar():
    global grammar
    global no_of_line
    j=0
    k=[]
    m=""
    file=open('F:\\Projects\\GLR\\grammar1.txt','r')
    if file is None:
        print("Error opening grammar.txt")
        exit(0)
    else:
        for line in file:
            no_of_line+=1
            line=line.rstrip('\n\r\t')
            left,right=line.rsplit('->')
            rightList=right.split('|')
            if no_of_line==1:
                grammar.append('Z'+'->'+left)
                gram_dic['Z'] = {left}
                start_symbol = left
            gram_dic[left] = set()
            for i in rightList:
                nonterminals.add(left)
                for c in i:
                    if re.search(r"[A-Z]",c):
                        nonterminals.add(c)
                    else:
                        terminals.add(c)
                grammar.append(left+'->'+ i)
                gram_dic[left].add(i)
    return grammar

def first_util(gram_symbol):
    firstset[gram_symbol] = set()
    if gram_symbol in terminals:
        firstset[gram_symbol].add(gram_symbol)
    else:
        for right_part in gram_dic[gram_symbol]:
            if(right_part[0] in terminals):
                firstset[gram_symbol].add(right_part[0])
            else:
                count = 0
                for sym in right_part:
                    if sym in terminals:
                        break
                    if sym == gram_symbol:
                        continue
                    for i in first_util(sym):
                        if i is not '^':
                            firstset[gram_symbol].add(i)
                    if '^' not in first_util(sym):
                        break
                    count+=1
                if count == len(right_part):
                    firstset[gram_symbol].add('^')
    return firstset[gram_symbol]

def first_string(string):
    req_set = set()
    count = 0
    for sym in string:
        if sym in terminals:
            req_set.add(sym)
            break
        for i in firstset[sym]:
            if i is not '^':
                req_set.add(i)
        if '^' not in firstset[sym]:
            break
        count+=1
    if count==len(string):
        req_set.add('^')
    return req_set

def follow_util(non_term):
    followset[non_term] = set()
    if non_term == 'Z':
        followset[non_term].add('$')
    for prod in grammar:
        if non_term in prod:
            if prod.find("->") < prod.find(non_term, 1):
                string = prod[prod.find(non_term, 1)+1:]
                for i in first_string(string):
                    if i is not '^':
                        followset[non_term].add(i)
                if not string or '^' in first_string(string):
                    if non_term is not prod[0]:
                        followset[non_term].update(follow_util(prod[0]))
    return followset[non_term]

def cal_first():
    for i in terminals:
        first_util(i)
    for i in nonterminals:
        first_util(i)

def cal_follow():
    followset['Z'] = {'$'}
    for i in nonterminals:
        follow_util(i)

def closure(items_set):
    clo_set = []
    for i in items_set:
        if i not in clo_set:
            clo_set.append(i)
    for item in items_set:
        dot_pos = item.find('.')
        temp_set = []
        if dot_pos < len(item)-1 and item[dot_pos+1] in nonterminals:
            for prod in grammar:
                if prod[0]==item[dot_pos+1]:
                    left = prod[0]
                    right = "." + prod[3:]
                    new_item = left + "->" + right
                    if prod[3] is not left:
                        if new_item not in temp_set:
                            temp_set.append(new_item)
                    if new_item not in clo_set:
                        clo_set.append(new_item)
        if temp_set:
            c = closure(temp_set)
            for i in c:
                if i not in clo_set:
                    clo_set.append(i)
    return clo_set

def shift_dot(string):
    left,right = string.rsplit('.')
    next_val = right[0]
    left = left + next_val
    new_right = "." + right[1:] 
    string = left + new_right
    return string

def create_states_util(state):
    count = 0
    if len(I[state])==1 and I[state][0][len(I[state][0])-1]=='.':
        item = I[state][0]
        item = item[:len(item)-1]
        index = grammar.index(item)
        look_up_red.append((state, item[0], index))
        return
    for item in I[state]:
        dot_pos = item.find('.')
        if dot_pos < len(item)-1:
            val = item[dot_pos+1]
            new_item = shift_dot(item)
            temp_tup = (state, val)
            flag = 0
            for a_tuple in look_up:
                if a_tuple[:2] == temp_tup:
                    flag = 1
                    #print("Flag value changed")
                    _set = closure([new_item])
                    for i in _set:
                        if i not in I[a_tuple[2]]:
                            I[a_tuple[2]].append(i)
                    break
            if flag==0:
                if len(I)>1:
                    last_state = I[len(I)-1]
                    i = 0
                    while i < len(I)- 1:
                        if I[i] == last_state:
                            I.pop()
                            count-=1
                            old_val = look_up[len(look_up)-1][1]
                            old_state = look_up[len(look_up)-1][0]
                            look_up.pop()
                            #print("Old value: " + old_val)
                            look_up.append((old_state, old_val, i))
                            break;
                        i+=1
                new_state = closure([new_item])
                I.append(new_state)
                look_up.append((state, val, len(I)-1))
                count+=1
        else:
            item = item[:len(item)-1]
            index = grammar.index(item)
            if item[0] is not 'Z':
                look_up_red.append((state, item[0], index))
            
    return count

def create_states():
    create_states_util(0)
    curr = 0
    for a_tuple in look_up:
        i = a_tuple[2]
        if i>curr:
            create_states_util(i)
            curr = i
            
    
    lookup_len = len(look_up)-1
    waste = look_up[len(look_up)-1][0]
    i = 0
    while waste != look_up[i][2] and i<=lookup_len:
        i+=1
    if i == lookup_len:
        while True:
            if look_up[lookup_len][0]==waste:
                look_up.pop()
                lookup_len-=1
            else:
                break
    else:
        i = 0
        last_state = I[len(I)-1]
        while i < len(I)- 1:
            if I[i] == last_state:
                #I.pop()
                old_val = look_up[len(look_up)-1][1]
                old_state = look_up[len(look_up)-1][0]
                look_up.pop()
                #print("Old value: " + old_val)
                look_up.append((old_state, old_val, i))
                break;
            i+=1
    I.pop()


def create_table():
    #global full_table
    global tables
    temp_tables=[]
    temp_table = {}
    for a_tuple in look_up:
        col = a_tuple[0]
        term = a_tuple[1]
        val = a_tuple[2]
        if col in table:
            if term in terminals:
                table[col][term] = ['s' + str(val)]
            else:
                table[col][term] = [str(val)]
        else:
            table[col] = {}
            if term in terminals:
                table[col][term] = ['s' + str(val)]
            else:
                table[col][term] = [str(val)]
    table[1]['$'] = ['A']
    #full_table = table
    tables.append(table)
    for a_tuple in look_up_red:
        col = a_tuple[0]
        nonterm = a_tuple[1]
        val = a_tuple[2]
        if col in table:
            for sym in followset[nonterm]:
                if sym in table[col]:
                    table_count = len(tables)
                    i = 0
                    while i<table_count:
                       
                        temp_table=deepcopy(tables[i])
                        temp_table[col][sym]=['r' + str(val)]
                        tables.append(temp_table)
                        i+=1
                   
                    #tables=temp_tables+tables
                    #full_table[col][sym].append('r' + str(val))
                else:
                    table[col][sym] = ['r' + str(val)]
                    #print(table)
            #        full_table[col][sym] = ['r' + str(val)]
        else:
            table[col] = {}
            for sym in followset[nonterm]:
                if sym in table[col]:
                    table[col][sym].append('r' + str(val))
                   # full_table[col][sym].append('r' + str(val))
                else:
                    table[col][sym] = ['r' + str(val)]
                    #full_table[col][sym] = ['r' + str(val)]    
    
def create_full_table():
    temp_table = {}
    for a_tuple in look_up:
        col = a_tuple[0]
        term = a_tuple[1]
        val = a_tuple[2]
        if col in full_table:
            if term in terminals:
                full_table[col][term] = ['s' + str(val)]
            else:
                full_table[col][term] = [str(val)]
        else:
            full_table[col] = {}
            if term in terminals:
                full_table[col][term] = ['s' + str(val)]
            else:
                full_table[col][term] = [str(val)]
    #tables.apppend(table)
    for a_tuple in look_up_red:
        col = a_tuple[0]
        nonterm = a_tuple[1]
        val = a_tuple[2]
        if col in full_table:
            for sym in followset[nonterm]:
                if sym in full_table[col]:
                    full_table[col][sym].append('r' + str(val))
                else:
                    full_table[col][sym] = ['r' + str(val)]
        else:
            full_table[col] = {}
            for sym in followset[nonterm]:
                if sym in full_table[col]:
                    full_table[col][sym].append('r' + str(val))
                else:
                    full_table[col][sym] = ['r' + str(val)]
    full_table[1]['$'] = ['A']
    
def parse_util(line, xtable,flag):
    global output
    orig_line = line
    line=list(line)
    stack=['0']
    j=0
    i=''
    print(xtable)
    m=xtable[int(stack[-1])][line[0]]
    count = 0
    try:
        while xtable[int(stack[-1])][line[0]][0]!='A':
            if flag==1:
                output.write("".join(stack))
                x=20-len("".join(stack))
                for k in range(x):
                    output.write(" ")
                output.write("".join(line))
                x=20-len("".join(line))
                for k in range(x):
                    output.write(" ")
            
            if xtable[int(stack[-1])][line[0]][0][0]=='s':
                stack.append(line[0])
                #output.write(strline+"\t")
                #print(stack)
                t=xtable[int(stack[-2])][line[0]][0][1:]
                if flag==1:
                    output.write('s'+t+"\t")
                    output.write("\n")
                stack.append(t)
                line.pop(0)
                
            elif xtable[int(stack[-1])][line[0]][0][0]=='r': 
                i=xtable[int(stack[-1])][line[0]][0][1:]
                i=int(i)
                
                production=gram[i].split('->')
                for j in range(2*len(production[1])):
                    #print(stack)
                    stack.pop()    
                stack.append(production[0])
                #print(stack)
                #print("#")
                no_to_reduce=xtable[int(stack[-2])][stack[-1]][0]
                stack.append(no_to_reduce)
                if flag==1:
                    output.write("r"+no_to_reduce+"\t")
                    output.write("("+gram[i]+")")
                    output.write("\n")
        if flag==1:
            output.write("".join(stack))
            x=20-len("".join(stack))
            for k in range(x):
                output.write(" ")
            output.write("".join(line))
            x=20-len("".join(line))
            for k in range(x):
                output.write(" ")
            output.write("Accepted")
        return True
    except Exception as e:
        #traceback.print_exc()
        return False
        #count+=1
        #print(orig_line + " Rejected")
        
        
def print_accept_table(line, xtable):
    output.write("\nTable used during parsing:\n\n")
    print_table(xtable)
    output.write("\nStepwise Parsing:\n\n")
    parse_util(line,xtable,1)
        
def parse():
    file=open('F:\\Projects\\GLR\\input.txt','r')
    if file is None:
        print("Error opening input.txt")
        exit(0)
    else:
        for line in file:
            count = 0
            for xtable in tables:
                if parse_util(line, xtable,0):
                    print_accept_table(line, xtable)
                    output.write("\n\n********* " + line + " Accepted " + "*********\n\n")
                    
                else:
                    count+=1
            if count == len(tables):
                output.write("\n\n********* " + line + " Rejected " + "*********\n\n")
    
def print_table(xtable):
    global output
    for i in xtable:
        output.write(str(i) + "\t")
        for sym in xtable[i]:
            output.write(sym + ":")
            for j in xtable[i][sym]:
                output.write(" "+j)
            output.write("\t")
        output.write("\n")
    
def print_states():
    output.write("States:\n\n")
    for i in I:
        for j in i:
            output.write(j + "\t")
        output.write("\n")
    
def main():
    global nonterminals
    global terminals
    global gram
    global output
    global full_table
    output=open('F:\\Projects\\GLR\\output.txt','w')
    gram=read_grammar()
    cal_first()
    cal_follow()
    I.append(closure(["Z->." + grammar[0][3]]))
    create_states()
    output.write("Terminals:\n\n")
    for i in terminals:
        output.write(i + " ")
    output.write("\n\nNon-terminals:\n\n")
    for i in nonterminals:
        output.write(i + " ")
    output.write("\n\nFirst Set:\n\n")
    for i in firstset:
        output.write(i + ": ")
        for j in firstset[i]:
            output.write(j + " ")
        output.write("\n")
    output.write("\nFollow Set:\n\n")
    for i in followset:
        output.write(i + ": ")
        for j in followset[i]:
            output.write(j + " ")
        output.write("\n")
    output.write("\n\n")
    print_states()
    create_table()
    create_full_table()
    output.write("\n\nParsing Table:\n\n")
    print_table(full_table)
    parse()
    print(nonterminals)
    print(terminals)
    print(firstset)
    print(followset)
if __name__=='__main__':
    main()
