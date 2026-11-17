-- Prove2me | Theorems.Thm_N25_Alg_charpoly_eq_cyclotomic_sq
-- name    : N25.Alg.charpoly_eq_cyclotomic_sq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:15.231443+00:00
-- url     : https://prove2.me/theorems/9f37976a-34f3-46f9-bb11-c3229af254ba
-- title:
--   An eight-dimensional operator annihilated by $Φ_5$ has characteristic polynomial $Φ_5^2$
-- statement:
--   Let $A$ be an $8×8$ rational matrix. If the fifth cyclotomic polynomial annihilates $A$, namely $Φ_5(A)=0$, then $$\chi_A(T)=Φ_5(T)^2.$$ This determines the characteristic polynomial of the order-five automorphism on the relevant eight-dimensional space.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false

theorem N25.Alg.charpoly_eq_cyclotomic_sq (A : Matrix (Fin 8) (Fin 8) ℚ)
    (hA : Polynomial.aeval A (Polynomial.cyclotomic 5 ℚ) = 0) :
    A.charpoly = (Polynomial.cyclotomic 5 ℚ) ^ 2 := by sorry
