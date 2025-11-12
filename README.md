Theorem “Adding₂”:
      m = m₀ ∧ n = n₀
    ⇒⁅  while m ≠ 0
          do
            m := m - 1 ⍮
            n := n + 1
          od
      ⁆
      n = m₀ + n₀
Proof:
    m = m₀ ∧ n = n₀
  ≡⟨ “Identity of +” ⟩ 
    m = m₀ ∧ n + 0 = n₀ + 0
  ≡⟨ “Unary minus” ⟩ 
    m = m₀ ∧ n + m + - m = n₀ + m + - m
  ≡⟨ “Cancellation of +” ⟩
    m = m₀ ∧ n + m = n₀ + m
  ≡⟨ “Abbreviated replacement”, substitution ⟩
    m = m₀ ∧ n + m = n₀ + m₀    
  ⇒⟨ “Weakening” ⟩
    m + n = m₀ + n₀
  ⇒⁅  while m ≠ 0
          do
            m := m - 1 ⍮
            n := n + 1
          od
      ⁆ 
  
  ⟨ “While” with subproof:
              (m ≠ 0) ∧ (m + n = m₀ + n₀)
            ⇒⟨ “Strengthening” ⟩
              (m + n = m₀ + n₀)
            =⟨ “Identity of +” ⟩
              (m + 0 + n = m₀ + n₀)
            =⟨ “Unary minus” ⟩ 
              (m + - 1 + 1 + n = m₀ + n₀)
            =⟨ “Subtraction” ⟩
              (m - 1 + 1 + n = m₀ + n₀) 
            =⟨ “Symmetry of +” ⟩
              (m - 1 + n + 1 = m₀ + n₀)              
            ⇒⁅ m := m - 1 ⁆ ⟨ “Assignment” with Substitution ⟩
              (m + n + 1 = m₀ + n₀)
            ⇒⁅ n := n + 1 ⁆ ⟨ “Assignment” with Substitution ⟩
              m + n = m₀ + n₀
    ⟩
    ¬ (m ≠ 0) ∧ (m + n = m₀ + n₀) 
  =⟨ “Definition of ≠” ⟩  
    ¬ ¬ (m = 0) ∧ (m + n = m₀ + n₀) 
  =⟨ “Double negation” ⟩
    (m = 0) ∧ (m + n = m₀ + n₀) 
  =⟨ “Abbreviated replacement”, Substitution ⟩
    (m = 0) ∧ (0 + n = m₀ + n₀) 
  ⇒⟨ “Weakening” ⟩   
    (0 + n = m₀ + n₀) 
  =⟨ “Identity of +” ⟩ 
    n = m₀ + n₀
    
------------------

Theorem “Answering...”:
      true
    ⇒⁅  i := 0 ⍮
        while i = 0
          do
            n := n + 1
          od
      ⁆
      n = 42
Proof:
    true
  =⟨ “Reflexivity of =” ⟩
    (0 = 0)
  =⟨ Substitution ⟩
    (i = 0) [i ≔ 0]
  ⇒⁅ i := 0 ⁆⟨“Assignment”⟩
    i = 0
  ⇒⁅
        while i = 0
          do
            n := n + 1
          od
      ⁆ 
   ⟨ “While” with subproof:
              i = 0 ∧ i = 0
            =⟨ “Idempotency of ∧” ⟩
              i = 0
            =⟨ Substitution ⟩
              (i = 0)[n ≔ n + 1]
            ⇒⁅ n := n + 1 ⁆ ⟨“Assignment”⟩                             
              i = 0
    ⟩
    ¬(i = 0) ∧ (i = 0)
  =⟨ “Contradiction” ⟩
    false
  ⇒⟨ “ex falso quodlibet” ⟩
    n = 42   
---------------------




              
