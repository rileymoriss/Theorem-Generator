#Symbols of the logic
primitives = ["(",")", "¬", "⇒", "=", "ε", "∀", "∧", "∨", "⇔", "∃"]
variables = ["u","w", "x", "y", "z"]

def get_fresh_variable(variable_list):
    guess = "x"
    while guess in variable_list:
      guess = guess + "'"
    return guess

def get_variables(formula):
    for prim in primitives:
        formula = formula.replace(prim, ' ')
    return formula.split()

def variable_substitution(formula,fresh,free):
    '''
    Jech is not careful if his substitutions are only for free variables or not?
    This obviously doesnt check for freeness, but maybe ill look into it.
    '''
    return formula.replace(free, fresh)
    
axioms = ["(∀x)(∀y)((∀z)((zεx)⇔(zεy))⇒(x=y))", #Extension
          "(∀x)(∀y)(∃z)(∀w)((xεz)⇔((w=x)∨(w=y)))", #Pairing
          "(∀x)(∃y)(∀u)((uεy)⇔((∃z)((zεx)∧(uεz))))", #Union
          "(∀x)(∃y)(∀u)((uεy)⇔((∀w)((wεu)⇒(wεx))))", #Power sets
          "(∃z)(((∀u)((uεa)⇔((yεy)∧¬(yεy)))⇒(aεz))∧((∀x)((xεz)⇒((∀u)((uεb)⇔((u=x)∨(uεx)))⇒(bεz)))))"] #Infinity

#Axiom Schemas
def axiom_schema_comprehension(formula):
    '''
    Jech gives a version of the axiom only valid for formulas with two free
    variables, the more general one is then provable. This turns out to be
    convenient for me.
    '''
    free = get_variables(formula)
    fresh = get_fresh_variable(free)
    fresh2 = get_fresh_variable(free + [fresh])

    #There is an axiom for both of the free variables
    axiom_of_comprehension = ["(∀"+fresh+")(∀"+free[0]+")(∃"+fresh2+free[-1]+")(("+free[-1]+
                  "ε"+fresh2+")⇔(("+free[-1]+"ε"+fresh+")∧"+formula+"))",
                              "(∀"+fresh+")(∀"+free[-1]+")(∃"+fresh2+free[0]+")(("+free[0]+
                  "ε"+fresh2+")⇔(("+free[0]+"ε"+fresh+")∧"+formula+"))"]
    return axiom_of_comprehension

def axiom_schema_replacement(formula):
    '''
    Jech states this for a formula with 3 free variables.
    That would mean that there are 3!= 6 axioms for each formula...
    '''
    free = get_variables(formula)
    fresh = get_fresh_variable(free)
    fresh2 = get_fresh_variable(free + [fresh])
    fresh3 = get_fresh_variable(free + [fresh, fresh2])

    #For now we only return one of them, we can just permute the variables in
    #the input to get all of them anyway.
    axiom_of_replacement = ["((∀"+free[0]+")(∀"+free[1]+")(∀"+fresh+")((("+
                            formula+")∧("+variable_substitution(formula,fresh,free[1])+
                            "))⇒("+free[1]+"="+fresh+")))⇒((∀"+fresh2+")(∃"+fresh3+
                            ")(∀"+free[1]+")(("+free[1]+"ε"+fresh3+")⇔(∃"+
                            free[0]+"(("+free[0]+"ε"+fresh2+")∧("+formula+")))))"]

    return axiom_of_replacement
    
def form_in(formula1, formula2):
  return formula1+"ε"+formula2

def form_equal(formula1, formula2):
  return formula1+"="+formula2

def form_and(formula1, formula2):
  return "("+formula1+")"+"∧"+"("+formula2+")"

def form_or(formula1, formula2):
  return "("+formula1+")"+"∨"+"("+formula2+")"

def form_if(formula1, formula2):
  return "("+formula1+")"+"⇒"+"("+formula2+")"

def form_iff(formula1, formula2):
  return "("+formula1+")"+"⇔"+"("+formula2+")"

def form_not(formula):
  return "¬"+"("+formula+")"

def form_forall(formula, variable=None):
  if variable == None:
    variable = random.choices([get_fresh_variable(formula)] + get_variables(formula), k=1)[0]
  return "(∀"+variable+")("+formula+")"

def form_exists(formula, variable=None):
  if variable == None:
    variable = random.choices([get_fresh_variable(formula)] + get_variables(formula), k=1)[0]
  return "(∃"+variable+")("+formula+")"

formula_formations = [form_and, form_or, form_if, form_iff, form_not, form_forall, form_exists]

#Identity Group
def sequent_identity(formula):
  return [formula, form_not(formula)]

def sequent_cut(sequent1, sequent2, index1, index2):
  #Should I check that the two things can be cut?
  sequent1.pop(index1)
  sequent2.pop(index2)
  return [sequent1, sequent2]

#Structural Rules
def sequent_weak(sequent, formula):
  return [sequent, formula]

def sequent_contract(sequent, index):
  #Should I check that its actually repeated
  sequent.pop(index)
  return sequent

#Logical Rules
def sequent_and(sequent1, sequent2, index1, index2):
  #should I check that the rest of the sequent is the same??
  formula = sequent1.pop(index1)
  sequent2[index2] = form_and(formula, sequent2[index2])
  return sequent2

def sequent_left_or(sequent, formula, index):
  sequent[index] = form_or(sequent[index], formula)
  return sequent

def sequent_right_or(sequent, formula, index):
  sequent[index] = form_or(formula, sequent[index])
  return sequent

#Quantifiers
def sequent_forall(sequent, index, variable):
  sequent[index] = form_forall(sequent[index], variable)
  return sequent

def sequent_exist(sequent, index, fresh, free):
  #Should I check that the variables are freee...
  sequent[index] = variable_substitution(sequent[index],fresh,free)
  sequent[index] = form_exists(sequent[index], fresh)
  return sequent

calculus_formations = [sequent_identity, sequent_cut, sequent_weak, sequent_contract, sequent_and, sequent_left_or,
                       sequent_right_or, sequent_forall, sequent_exist]

parity_two_formation = [form_and, form_or, form_if, form_iff]
parity_one_formation = [form_not, form_forall, form_exists]
import random

def get_formula(size = (0, 0), seed = None):
  random.seed(a=seed)
  rand_size = (random.randint(min_size, max_size), random.randint(min_size, max_size))
  if 0 in size:
    #Do a random size
    return get_formula(rand_size)
  else:
    #Set the variables in play
    num_var = max(1, round(random.gauss(mu=size[0], sigma=0.1*size[0]))) #even for pairing
    variables_local = ['x']
    for i in range(num_var):
      variables_local.append(get_fresh_variable(variables_local))


    #Set the atoms
    atoms_local = []
    for i in range(num_var*2): #could add more randomness
      pair_local = random.choices(variables_local, k=2) #with replacement
      if random.random() < 0.5:
        atoms_local.append(form_equal(pair_local[0], pair_local[1]))
      else:
        atoms_local.append(form_in(pair_local[0], pair_local[1]))

    #Set the moves to make
    formed_strings = []
    new_atoms = []

    #unary operations
    for atom in atoms_local:
      for i in range(random.randint(0, max(1, round(random.gauss(mu=10, sigma=2))))):
        apply_this = random.choices(parity_one_formation, k=1)[0]
        atom = apply_this(atom)
      new_atoms.append(atom)

    while len(new_atoms) >1:
      indexes = random.choices(range(len(new_atoms)), k=2)
      apply_to_these = [new_atoms[i] for i in range(len(new_atoms)) if i in indexes]
      if len(apply_to_these) ==1:
        apply_to_these = apply_to_these+apply_to_these
      new_atoms = [new_atoms[i] for i in range(len(new_atoms)) if i not in indexes]
      apply_this = random.choices(parity_two_formation, k=1)[0]
      new_atoms.append(apply_this(apply_to_these[0], apply_to_these[1]))

    #Should do it like this: unary, binary, unary, binary etc
    
    return new_atoms

min_size = int(input("Minimum Size:")) #must be greater than 0
max_size = int(input("Maximum Size:"))
text = get_formula()[0]
#print(text)
# Open a file in write mode ('w')
file = open('C:/Users/riley/My Drive/Active Projects/ZFC/output.txt', 'w', encoding="utf-8")
    # Write the string to the file
file.write(text)
file.close()