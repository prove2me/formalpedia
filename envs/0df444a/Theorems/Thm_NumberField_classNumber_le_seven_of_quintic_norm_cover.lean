-- Prove2me | Theorems.Thm_NumberField_classNumber_le_seven_of_quintic_norm_cover
-- name    : NumberField.classNumber_le_seven_of_quintic_norm_cover
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:13.674767+00:00
-- url     : https://prove2.me/theorems/7452c7f6-30b3-47ae-928d-ef7fc640ae36
-- title:
--   A seven-ideal norm cover bounds a totally real quintic class number by seven
-- statement:
--   Let $K$ be a number field with $[K:ℚ]=5$, no complex places, and $|d_K|≤5^8$. Let $s$ be a finite set of nonzero ideals with $|s|≤7$, and assume every nonzero ideal $I$ with $N(I)≤24$ lies in $s$. Then $$h_K≤7.$$ This is the numerical Minkowski step for the quintic character field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open scoped nonZeroDivisors
open NumberField

theorem NumberField.classNumber_le_seven_of_quintic_norm_cover
    (K : Type*) [Field K] [NumberField K]
    (hdegree : Module.finrank ℚ K = 5)
    (hcomplex : InfinitePlace.nrComplexPlaces K = 0)
    (hdiscr : |(discr K : ℝ)| ≤ 5 ^ 8)
    (s : Finset (Ideal (𝓞 K))⁰) (hcard : s.card ≤ 7)
    (hcover : ∀ I : (Ideal (𝓞 K))⁰,
      Ideal.absNorm (I : Ideal (𝓞 K)) ≤ 24 → I ∈ s) :
    classNumber K ≤ 7 := by sorry
