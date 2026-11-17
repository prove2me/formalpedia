-- Prove2me | Theorems.Thm_N25_Alg_det_cyclotomic_prime
-- name    : N25.Alg.det_cyclotomic_prime
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:15.92001+00:00
-- url     : https://prove2.me/theorems/6d43c1ab-cea0-4e5b-b22b-e93c93194abe
-- title:
--   The cyclotomic determinant computation gives $71^2$
-- statement:
--   Let $A$ be an $8×8$ integer matrix whose rational characteristic polynomial is $Φ_5(T)^2$. Then $$\det(2I_8+4A+A^2)=71^2.$$ This identifies the order of the kernel of the endomorphism used in the $71$-isogeny.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false

theorem N25.Alg.det_cyclotomic_prime (A : Matrix (Fin 8) (Fin 8) ℤ)
    (hA : (A.map (Int.castRingHom ℚ)).charpoly = (Polynomial.cyclotomic 5 ℚ) ^ 2) :
    Matrix.det ((2 : ℤ) • (1 : Matrix (Fin 8) (Fin 8) ℤ) + (4 : ℤ) • A + A * A) =
      (71 : ℤ) ^ 2 := by sorry
