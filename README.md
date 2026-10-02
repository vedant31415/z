Idempotency of ∧”: p ∧ p ≡ p
“Golden rule”: p ∧ q ≡ (p ≡ (q ≡ p ∨ q))
Contradiction”: p ∧ ¬ p ≡ false
“Definition of ⇒”: p ⇒ q ≡ (p ∨ q ≡ q)
Unary minus”: a + - a = 0
(3.32): p ∨ q ≡ (p ∨ ¬ q ≡ p)
---
Theorem “Shifting `suc` over +”: suc m + n = m + suc n
Proof:
  By induction on `m : ℕ`:
    Base case:
        suc 0 + n
      =⟨ “Definition of + for `suc`” ⟩
        suc (0 + n)
      = ⟨ “Definition of + for 0” ⟩
        suc n
      = ⟨ “Left-identity of +” ⟩ 
        0 + suc n
    Induction step:
        suc (suc m) + n
      =⟨ “Definition of + for `suc`” ⟩
        suc (suc m + n)
      =⟨ Induction hypothesis ⟩
        suc (m + suc n)
      =⟨ “Definition of + for `suc`” ⟩ 
        suc m + suc n
----------
Lemma (A1.2b):       (p ∧ q ≡ p₀ ∧ q₀) ∧ (p ∨ q ≡ p₀ ∨ q₀)
                 ⇒⁅  p := p ≡ q
                   ⍮ q := (p ≡ q) ∨ q
                   ⍮ p := p ≡ q
                   ⁆
                     (p ≡ p₀ ∧ q₀) ∧ (q ≡ p₀ ∨ q₀)
Proof:
    (p ∧ q ≡ p₀ ∧ q₀) ∧ (p ∨ q ≡ p₀ ∨ q₀)
  ≡ ⟨ “Golden rule” ⟩ 
    (p ≡ q ≡ ((p) ∨ q) ≡ p₀ ∧ q₀) ∧ (((p) ∨ q) ≡ p₀ ∨ q₀)    
  ≡ ⟨ “Identity of ≡” ⟩ 
    (p ≡ q ≡ ((p ≡ true) ∨ q) ≡ p₀ ∧ q₀) ∧ (((p ≡ true) ∨ q) ≡ p₀ ∨ q₀)
  ≡ ⟨ “Identity of ≡” ⟩
    (p ≡ q ≡ ((p ≡ q ≡ q) ∨ q) ≡ p₀ ∧ q₀) ∧ (((p ≡ q ≡ q) ∨ q) ≡ p₀ ∨ q₀)
  ≡ ⟨ Substitution ⟩
    ((p ≡ ((p ≡ q) ∨ q) ≡ p₀ ∧ q₀) ∧ (((p ≡ q) ∨ q) ≡ p₀ ∨ q₀))[p ≔ p ≡ q]
  ⇒⁅ p := p ≡ q ⁆ ⟨“Assignment” ⟩ 
    (p ≡ ((p ≡ q) ∨ q) ≡ p₀ ∧ q₀) ∧ (((p ≡ q) ∨ q) ≡ p₀ ∨ q₀)
  ≡ ⟨ Substitution ⟩  
    ((p ≡ q ≡ p₀ ∧ q₀) ∧ (q ≡ p₀ ∨ q₀)) [q ≔ (p ≡ q) ∨ q]
  ⇒⁅ q := (p ≡ q) ∨ q ⁆ ⟨ “Assignment” ⟩ 
    (p ≡ q ≡ p₀ ∧ q₀) ∧ (q ≡ p₀ ∨ q₀)
  ≡ ⟨ Substitution ⟩ 
    ((p ≡ p₀ ∧ q₀) ∧ (q ≡ p₀ ∨ q₀))[p ≔ p ≡ q]
  ⇒⁅ p := p ≡ q ⁆ ⟨ “Assignment” ⟩ 
    (p ≡ p₀ ∧ q₀) ∧ (q ≡ p₀ ∨ q₀)
---------------------
Theorem “Reflexivity of ≤”: a ≤ a
Proof:
  By induction on `a : ℕ`:
    Base case:
        0 ≤ 0
      ≡ ⟨ “Zero is least element” ⟩
        true
    Induction step:
        suc a ≤ suc a
      ≡ ⟨ “Isotonicity of successor” ⟩
        a ≤ a
      ≡ ⟨ Induction hypothesis ⟩ 
        true
------------------
Theorem “Antisymmetry of ≤”: a ≤ b ⇒ b ≤ a ⇒ a = b
Proof:
  By induction on `a : ℕ`:
    Base case `0 ≤ b ⇒ b ≤ 0 ⇒ 0 = b`:
        0 ≤ b ⇒ b ≤ 0 ⇒ 0 = b
      ≡⟨ “Zero is least element” ⟩
        true ⇒ b ≤ 0 ⇒ 0 = b
      ≡⟨ “Zero is unique least element” ⟩
        true ⇒ b = 0 ⇒ 0 = b
      ≡⟨ “Reflexivity of ⇒” ⟩  
        true
    Induction step `suc a ≤ b ⇒ b ≤ suc a ⇒ suc a = b`:
      By induction on `b : ℕ`:
        Base case `suc a ≤ 0 ⇒ 0 ≤ suc a ⇒ suc a = 0`:
            suc a ≤ 0 ⇒ 0 ≤ suc a ⇒ suc a = 0
          ≡⟨ “Successor is not at most zero” ⟩
            false ⇒ 0 ≤ suc a ⇒ suc a = 0
          ≡⟨ “ex falso quodlibet” ⟩ 
            true
        Induction step `suc a ≤ suc b ⇒ suc b ≤ suc a ⇒ suc a = suc b`:
            suc a ≤ suc b ⇒ suc b ≤ suc a ⇒ suc a = suc b
          ≡⟨ “Isotonicity of successor” ⟩
            a ≤ b ⇒ suc b ≤ suc a ⇒ suc a = suc b
          ≡ ⟨ “Isotonicity of successor” ⟩ 
            a ≤ b ⇒ b ≤ a ⇒ suc a = suc b            
          ≡ ⟨ “Cancellation of `suc`” ⟩  
            a ≤ b ⇒ b ≤ a ⇒ a = b
          ≡ ⟨ Induction hypothesis `a ≤ b ⇒ b ≤ a ⇒ a = b` ⟩ 
            true
----------------------
Theorem (3.19) “Mutual interchangeability of ≡ with ≢”:
   (p ≢ q ≡ r) ≡ (p ≡ q ≢ r)
Proof:
    (p ≢ q ≡ r) 
  ≡ ⟨ “Definition of ≢” ⟩ 
    ¬ (p ≡ q ≡ r)
  ≡ ⟨ “¬ connection” ⟩
    (p ≡ ¬ q ≡ r)
  ≡ ⟨ (3.14) ⟩ 
    (p ≡ q ≢ r)
--------------
Theorem (3.30) “Identity of ∨”: p ∨ false ≡ p
Proof:
    p ∨ false ≡ p
  ≡ ⟨ “Idempotency of ∨” ⟩
    p ∨ false ≡ p ∨ p
  ≡ ⟨ “Distributivity of ∨ over ≡” ⟩
    p ∨ (false ≡ p)
  ≡ ⟨ (3.15) ⟩
    p ∨ ¬ p 
  ≡ ⟨ “Excluded middle” ⟩ 
    true
--------------
Theorem (3.32): p ∨ q ≡ p ∨ ¬ q ≡ p
Proof:
    p ∨ q ≡ p ∨ ¬ q ≡ p
  ≡ ⟨ “Distributivity of ∨ over ≡” ⟩
    p ∨ (q ≡ ¬ q) ≡ p
  ≡ ⟨ (3.15) ⟩
    p ∨ false ≡ p
  ≡ ⟨ “Identity of ∨” ⟩  
    p ≡ p
  ≡ ⟨ “Identity of ≡” ⟩ 
    true
--------------
Theorem (3.46) “Distributivity of ∧ over ∨”: p ∧ (q ∨ r) ≡ (p ∧ q) ∨ (p ∧ r)
Proof:
    p ∧ (q ∨ r) 
  ≡ ⟨ “Absorption” ⟩ 
    (p ∧ (p ∨ r)) ∧ (q ∨ r)
  ≡ ⟨ “Distributivity of ∨ over ∧” ⟩ 
    p ∧ ((p ∧ q) ∨ r)
  ≡ ⟨ “Absorption” ⟩ 
    (p ∨ (p ∧ q)) ∧ ((p ∧ q) ∨ r)
  ≡ ⟨ “Distributivity of ∨ over ∧” ⟩
    (p ∧ q) ∨ (p ∧ r)
--------------
Theorem (3.48): p ∧ q ≡ p ∧ ¬ q ≡ ¬ p
Proof:
    p ∧ q ≡ p ∧ ¬ q ≡ ¬ p
  ≡ ⟨ “Golden rule” ⟩
    p ≡ q ≡ p ∨ q ≡ p ∧ ¬ q ≡ ¬ p
  ≡ ⟨ “Golden rule” ⟩ 
    p ≡ q ≡ (p ∨ q) ≡ p ≡ ¬ q ≡ (p ∨ ¬ q) ≡ ¬ p
  ≡ ⟨ (3.32) ⟩ 
    p ≡ q ≡ ¬ p ≡ ¬ q
  ≡ ⟨ “¬ connection” ⟩ 
    true
--------------
Theorem (3.62): p ⇒ (q ≡ r) ≡ p ∧ q ≡ p ∧ r
Proof:
    p ⇒ (q ≡ r)
  ≡ ⟨ “Definition of ⇒” ⟩
    p ∨ (q ≡ r) ≡ (q ≡ r)
  ≡ ⟨ “Distributivity of ∨ over ≡” ⟩ 
    p ∨ q ≡ p ∨ r ≡ (q ≡ r)
  ≡ ⟨ “Golden rule” ⟩
    p ∧ q ≡ p ∧ r
--------------
Theorem (3.65) “Shunting”: p ∧ q ⇒ r ≡ p ⇒ (q ⇒ r)
Proof:
    p ∧ q ⇒ r
  ≡ ⟨ “Definition of ⇒” ⟩
    ¬(p ∧ q) ∨ r
  ≡ ⟨ “De Morgan” ⟩
    ¬ p ∨ ¬ q ∨ r
  ≡ ⟨ “Definition of ⇒” ⟩ 
    ¬ p ∨ (q ⇒ r)
--------------
Theorem (3.49) “Semi-distributivity of ∧ over ≡”: p ∧ (q ≡ r) ≡ p ∧ q ≡ p ∧ r ≡ p
Proof:
    p ∧ (q ≡ r) ≡ p ∧ q ≡ p ∧ r ≡ p
  ≡ ⟨ “Golden rule” ⟩ 
    p ≡ (q ≡ r) ≡ p ∨ (q ≡ r) ≡ p ∧ q ≡ p ∧ r ≡ p
  ≡ ⟨ “Golden rule” ⟩ 
    p ≡ (q ≡ r) ≡ p ∨ (q ≡ r) ≡ p ≡ q ≡ p ∨ q ≡ p ∧ r ≡ p
  ≡ ⟨ “Golden rule” ⟩ 
    p ≡ (q ≡ r) ≡ p ∨ (q ≡ r) ≡ p ≡ q ≡ p ∨ q ≡ p ≡ r ≡ p ∨ r ≡ p
  ≡ ⟨ “Distributivity of ∨ over ≡” ⟩ 
    p ≡ q ≡ r ≡ p ∨ q ≡ p ∨ r ≡ p ≡ q ≡ p ∨ q ≡ p ≡ r ≡ p ∨ r ≡ p
  ≡ ⟨ “Identity of ≡” ⟩ 
    true
  ≡ ⟨ “Definition of ⇒” ⟩ 
    p ⇒ (q ⇒ r)
--------------
Theorem (3.70): p ∨ q ⇒ p ∧ q ≡ p ≡ q
Proof:
    p ∨ q ⇒ p ∧ q
  ≡ ⟨ “Definition of ⇒” ⟩
    (p ∨ q) ∨ (p ∧ q) ≡ p ∧ q   
  ≡ ⟨ “Absorption” ⟩ 
    p ∨ q ≡ p ∧ q
  ≡ ⟨ “Golden rule” ⟩ 
    p ≡ q
--------------
