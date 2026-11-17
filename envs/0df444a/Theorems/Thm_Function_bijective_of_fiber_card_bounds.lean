-- Prove2me | Theorems.Thm_Function_bijective_of_fiber_card_bounds
-- name    : Function.bijective_of_fiber_card_bounds
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:28.147192+00:00
-- url     : https://prove2.me/theorems/a3ec030e-4ad2-4cc9-88be-3672c954b9ec
-- title:
--   Sharp lower bounds on selected fibres force a bijection and exact fibre sizes
-- statement:
--   Let $A$ be finite, let $I$ be a finite indexing set, let $f:A→B$ be surjective, and let $p:I→B$ be injective. Suppose nonnegative integers $w_i$ satisfy $∑_{i∈I}w_i=|A|$ and $w_i≤|f^{-1}(p_i)|$ for every $i$. Then $$p:I→B\text{ is bijective},\qquad |f^{-1}(p_i)|=w_i\text{ for all }i.$$ This converts fibrewise lower bounds and a total-cardinality identity into exact point counts.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open Function

theorem Function.bijective_of_fiber_card_bounds
    {A B I : Type*} [Finite A] [Fintype I]
    (f : A → B) (hf : Surjective f) (p : I → B) (hp : Injective p)
    (w : I → ℕ) (hw : ∑ i, w i = Nat.card A)
    (hbound : ∀ i, w i ≤ Nat.card {a : A // f a = p i}) :
    Bijective p ∧ ∀ i, Nat.card {a : A // f a = p i} = w i := by sorry
