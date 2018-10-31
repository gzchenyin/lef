from z3 import *
from random import shuffle, randint
from time import process_time
from os import listdir
import signal

def signal_handler(signum, frame):
    raise Exception("Timed out!")

def lef_instance(file_name, agent_num, goods_num, edge_num):
    of = open(file_name, 'w')
    of.writelines(str(agent_num) + ' ' + 
        str(goods_num) + ' ' + str(edge_num) + '\n')
    
    a = [i for i in range(1, goods_num+1)]
    for i in range(agent_num):
        shuffle(a)
        for j in a:
            of.write(str(j) + ' ')
        of.write('\n')
    
    e = set()
    while (len(e) < edge_num):
        x = randint(1, agent_num)
        y = randint(1, agent_num)
        if x != y:
            if x > y:
                x, y = y, x
            e.add((x,y))


    for (i, j) in e:
        of.write(str(i) + ' ' + str(j) + '\n')

    of.close()

def ins_read(file_name):
    of = open(file_name, 'r')

    line = of.readline()
    [agent_num, goods_num, edge_num] = [int(n) for n in line.split(' ')]

    weight = []
    for i in range(agent_num):
        line = of.readline().rstrip('\n').rstrip(' ')
        r = [int(n) for n in line.split(' ')]
        weight.append(r)
    
    graph = []
    for i in range(edge_num):
        line = of.readline().rstrip('\n').rstrip(' ')
        [x, y] = [int(n) for n in line.split(' ')]
        graph.append((x,y))

    of.close()
    return weight, graph

def ins_create(agent_num, goods_num, edge_num):
    weight = []
    a = [i for i in range(1, goods_num+1)]
    for i in range(agent_num):
        shuffle(a)
        weight.append(a.copy())
    
    graph = set()
    if edge_num * 2 < agent_num * (agent_num -1) /2:
        en = edge_num
    else:
        en = agent_num * (agent_num -1) /2 - edge_num

    while (len(graph) < en):
        x = randint(1, agent_num)
        y = randint(1, agent_num)
        if x != y:
            if x > y:
                x, y = y, x
            graph.add((x,y))

    if edge_num * 2 < agent_num * (agent_num -1) /2:
        graph1 = list(graph)
    else:
        graph1 = []
        for i in range(1, agent_num+1):
            for j in range(i+1, agent_num+1):
                if not ((i, j) in graph):
                    graph1.append((i,j))

    return weight, graph1
    
def ins_write(file_name, weight, graph):
    agent_num = len(weight)
    goods_num = len(weight[0])
    edge_num = len(graph)

    of = open(file_name, 'w')
    of.writelines(str(agent_num) + ' ' + 
        str(goods_num) + ' ' + str(edge_num) + '\n')
    
    for a in weight:
        for i in a:
            of.write(str(i) + ' ')
        of.write('\n')

    for (i, j) in graph:
        of.write(str(i) + ' ' + str(j) + '\n')

    of.close()

def ext_lef(weight, graph):
    tm = process_time()

    agent_num = len(weight)
    goods_num = len(weight[0])

    s = Solver()
    alloc = Function("alloc", IntSort(), IntSort())
    for i in range(1, agent_num+1):
         s.add(And(alloc(i) > 0, alloc(i) <= agent_num))
    s.add(Distinct([alloc(i) for i in range(1, agent_num+1)]))
    
    fw = Function("weight", IntSort(), IntSort(), IntSort())

    for i in range(1, agent_num+1):
        for j in range(1, goods_num+1):
            s.add(fw(i,j) == weight[i-1][j-1])
    
    for (i,j) in graph:
        s.add(fw(i, alloc(i)) <= fw(i, alloc(j)))
        s.add(fw(j, alloc(j)) <= fw(j, alloc(i)))

    r = str(s.check())
    return process_time()-tm, r

def max_agt(weight, graph):
    tm = process_time()

    agent_num = len(weight)
    goods_num = len(weight[0])

    s = Optimize()
    alloc = Function("alloc", IntSort(), IntSort())
    for i in range(1, agent_num+1):
         s.add(And(alloc(i) > 0, alloc(i) <= agent_num))
    s.add(Distinct([alloc(i) for i in range(1, agent_num+1)]))
    
    fw = Function("weight", IntSort(), IntSort(), IntSort())

    for i in range(1, agent_num+1):
        for j in range(1, goods_num+1):
            s.add(fw(i,j) == weight[i-1][j-1])
    
    cost = []
    for i in range(agent_num):
        cond = []
        for (u,v) in graph:
            if (i == u):
                ct = fw(u, alloc(u)) > fw(u, alloc(v))
                cond.append(ct)
            if (i == v):
                ct = fw(v, alloc(v)) > fw(v, alloc(u))
                cond.append(ct)
        cost.append(If(Or(*cond), 0, 1))
    
    sum = Int('sum')
    s.add(sum == Sum(*cost))
    h = s.maximize(sum)

    r = str(s.check())
    m = s.model()

    return process_time()-tm, r

def min_eny(weight, graph):
    tm = process_time()

    agent_num = len(weight)
    goods_num = len(weight[0])

    s = Optimize()
    alloc = Function("alloc", IntSort(), IntSort())
    for i in range(1, agent_num+1):
         s.add(And(alloc(i) > 0, alloc(i) <= agent_num))
    s.add(Distinct([alloc(i) for i in range(1, agent_num+1)]))
    
    fw = Function("weight", IntSort(), IntSort(), IntSort())

    for i in range(1, agent_num+1):
        for j in range(1, goods_num+1):
            s.add(fw(i,j) == weight[i-1][j-1])
    
    k = 0
    cost = []
    for (i,j) in graph:
        ct1 = If(fw(i, alloc(i)) <= fw(i, alloc(j)), 
            0, fw(i, alloc(i)) - fw(i, alloc(j)))
        cost.append(ct1)
        ct2 = If(fw(j, alloc(j)) <= fw(j, alloc(i)), 
            0, fw(j, alloc(j)) - fw(j, alloc(i)))
        cost.append(ct2)

    sum = Int('sum')
    s.add(sum == Sum(*cost))
    h = s.minimize(sum)

    r = str(s.check())
    m = s.model()

    return process_time()-tm, r


def ext_rel(weight, graph):
    tm = process_time()

    agent_num = len(weight)
    goods_num = len(weight[0])
    s = Solver()
    allo = Function("allo", IntSort(), IntSort())
    for i in range(1, agent_num+1):
         s.add(And(allo(i) > 0, allo(i) <= agent_num))
    s.add(Distinct([allo(i) for i in range(1, agent_num+1)]))
    
    fw = Function("weight", IntSort(), IntSort(), IntSort())

    for i in range(1, agent_num+1):
        for j in range(1, goods_num+1):
            s.add(fw(i,j) == weight[i-1][j-1])
    
    rel = Function("rel", IntSort(), IntSort())
    for i in range(1, agent_num+1):
        s.add(And(rel(i) > 0, rel(i) <= agent_num))
    s.add(Distinct([rel(i) for i in range(1, agent_num+1)]))

    for (i,j) in graph:
        s.add(fw(rel(i), allo(rel(i))) <= fw(rel(i), allo(rel(j))))
        s.add(fw(rel(j), allo(rel(j))) <= fw(rel(j), allo(rel(i))))

    r = str(s.check())
    return process_time()-tm, r

def lef1():
    repeat_num = 5
    dir_name = './example/lef1/'

    for agent_num in range(10, 41, 5):
        goods_num = agent_num
        for edge_ratio in range(10, 51, 10):
            tt = 0
            sat = 0
            ot = 0
            edge_num = int(agent_num*(agent_num-1)*edge_ratio/200)
            for i in range(repeat_num):
                file_name = '{}{:02d}-{:02d}-{:02d}-{:02d}'.format(
                    dir_name, agent_num, goods_num, edge_ratio, i+1
                )
                weight, graph = ins_create(agent_num, goods_num, edge_num)
                ins_write(file_name, weight, graph)

                signal.signal(signal.SIGALRM, signal_handler)
                signal.alarm(1200)   # in seconds
                try:
                    tm, result = ext_lef(weight, graph)
                except Exception:
                    tm, result = 0, '-'
                
                if tm == 0:
                    ot = 1
                if ot == 0:
                    tt = tt + tm
                    if result == 'sat':
                        sat = sat + 1
            
            if ot == 0:
                print('{:02d}-{:02d}-{:02d} {:>7.4f}({:d})'.format(
                    agent_num, goods_num, edge_ratio, tt/repeat_num, sat
                ))
            else:
                print('{:02d}-{:02d}-{:02d} timeout'.format(
                    agent_num, goods_num, edge_ratio
                ))

def lef2_gen():
    #generate unsat instance
    repeat_num = 5
    dir_name = './example/lef2/'

    for agent_num in range(10, 41, 5):
        goods_num = agent_num
        for edge_ratio in range(30, 41, 5):
            edge_num = int(agent_num*(agent_num-1)*edge_ratio/200)
            i = 0
            while (i < repeat_num):
                weight, graph = ins_create(agent_num, goods_num, edge_num)
                tm, result = ext_lef(weight, graph)

                if result == 'unsat':
                    file_name = '{}{:02d}-{:02d}-{:02d}-{:02d}'.format(
                        dir_name, agent_num, goods_num, edge_ratio, i+1
                        )
                    ins_write(file_name, weight, graph)
                    print('{:02d}-{:02d}-{:02d} {:>7.4f}'.format(
                        agent_num, goods_num, edge_ratio, tm
                    ))
                    i = i + 1

def lef2():
    result_file = 'result_lef2'
    of = open(result_file, 'w')

    dirname = './example/lef2/'
    
    filelist = os.listdir(dirname)
    filelist.sort()
    for filename in filelist:
        of.writelines(dirname+filename + '\n')
        of.flush()
        weight, graph = ins_read(dirname + filename)

        tm1, result1 = ext_lef(weight, graph)

        signal.signal(signal.SIGALRM, signal_handler)
        signal.alarm(1200)   # in seconds
        try:
            tm2, result2 = max_agt(weight, graph)
        except Exception:
            tm2, result2 = 0, '-'

        signal.signal(signal.SIGALRM, signal_handler)
        signal.alarm(1200)   # in seconds
        try:
            tm3, result3 = min_eny(weight, graph)
        except Exception:
            tm3, result3 = 0, '-'

        signal.signal(signal.SIGALRM, signal_handler)
        signal.alarm(1200)   # in seconds
        try:
            tm4, result4 = ext_rel(weight, graph)
        except Exception:
            tm4, result4 = 0, '-'

        s = '{:>7.4f}({}) {:>7.4f}({}) {:>7.4f}({}) {:>7.4f}({})'.format(
            tm1, result1, tm2, result2, tm3, result3, tm4, result4)
        of.writelines(s + '\n')
        of.flush()
    of.close()

def lef3():
    repeat_num = 5
    dir_name = './example/lef3/'

    result_file = 'result_lef3'
    of = open(result_file, 'w')

    for agent_num in range(10, 101, 5):
        goods_num = agent_num
        for edge_ratio in range(5, 11, 5):
            tt = 0
            sat = 0
            ot = 0
            edge_num = int(agent_num*(agent_num-1)*edge_ratio/200)
            for i in range(repeat_num):
                file_name = '{}{:02d}-{:02d}-{:02d}-{:02d}'.format(
                    dir_name, agent_num, goods_num, edge_ratio, i+1
                )
                weight, graph = ins_create(agent_num, goods_num, edge_num)
                ins_write(file_name, weight, graph)

                signal.signal(signal.SIGALRM, signal_handler)
                signal.alarm(1200)   # in seconds
                try:
                    tm, result = ext_lef(weight, graph)
                except Exception:
                    tm, result = 0, '-'
                print('{} {:>7.4f} {}'.format(
                       file_name, tm, result
                    ))
                                    
                if tm == 0:
                    ot = 1
                if ot == 0:
                    tt = tt + tm
                    if result == 'sat':
                        sat = sat + 1
            
            if ot == 0:
                s = '{:02d}-{:02d}-{:02d} {:>7.4f}({:d})'.format(
                    agent_num, goods_num, edge_ratio, tt/repeat_num, sat)
            else:
                s = '{:02d}-{:02d}-{:02d} timeout'.format(
                    agent_num, goods_num, edge_ratio)
            of.writelines(s + '\n')
            of.flush()
    of.close()

if __name__ == "__main__":
    lef1()
