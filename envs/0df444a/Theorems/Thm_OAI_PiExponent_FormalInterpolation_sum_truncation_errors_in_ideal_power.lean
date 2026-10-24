-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_sum_truncation_errors_in_ideal_power
-- name    : OAI.PiExponent.FormalInterpolation.sum_truncation_errors_in_ideal_power
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:07:46.811847+00:00
-- url     : https://prove2.me/theorems/715fb445-6750-4f69-95bb-130d22025ec3
-- title:
--   Combine the individual truncation errors
-- statement:
--   If each evaluated truncation error belongs to I^n, multiplying by b_i and summing preserves membership in I^n. The independent proof route is to rewrite the difference as the sum of the multiplied errors and use the ideal’s closure under addition and multiplication.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.sum_truncation_errors_in_ideal_power
    {d m t : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (n : Nat) (g : Fin m → MvPolynomial (Fin d) Complex)
    (b : Fin t → MvPolynomial (Fin d) Complex)
    (F G : Fin t → MvPolynomial (Fin m) Complex)
    (hFG : ∀ i, MvPolynomial.aeval g (F i - G i) ∈ I ^ n) :
    (∑ i : Fin t, MvPolynomial.aeval g (F i) * b i) -
      (∑ i : Fin t, MvPolynomial.aeval g (G i) * b i) ∈ I ^ n := by sorry
