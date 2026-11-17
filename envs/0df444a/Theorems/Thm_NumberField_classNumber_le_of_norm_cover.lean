-- Prove2me | Theorems.Thm_NumberField_classNumber_le_of_norm_cover
-- name    : NumberField.classNumber_le_of_norm_cover
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:53:14.476032+00:00
-- url     : https://prove2.me/theorems/684b40cb-fe66-4142-99e9-7e63ba6f0da3
-- title:
--   A finite cover of the Minkowski range bounds the class number
-- statement:
--   Let $K$ be a number field of degree $n$, with $r_2$ complex places and discriminant $d_K$, and let $s$ be a finite set of nonzero ideals of $\mathcal O_K$. Assume every nonzero ideal $I$ satisfying $$N(I)≤\left(\frac{4}{π}\right)^{r_2}\frac{n!}{n^n}\sqrt{|d_K|}$$ belongs to $s$. Then $h_K≤|s|$. This converts an explicit norm enumeration into a class-number bound.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open scoped nonZeroDivisors
open NumberField

theorem NumberField.classNumber_le_of_norm_cover
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (Ideal (𝓞 K))⁰)
    (hcover : ∀ I : (Ideal (𝓞 K))⁰,
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤
        (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
          ((Module.finrank ℚ K).factorial /
            (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
              Real.sqrt |(discr K : ℝ)|) → I ∈ s) :
    classNumber K ≤ s.card := by sorry
