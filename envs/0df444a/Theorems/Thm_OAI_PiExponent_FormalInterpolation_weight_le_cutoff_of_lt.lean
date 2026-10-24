-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_weight_le_cutoff_of_lt
-- name    : OAI.PiExponent.FormalInterpolation.weight_le_cutoff_of_lt
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:47:00.928704+00:00
-- url     : https://prove2.me/theorems/57d1527a-edb0-4ec3-b5ab-b2409e91df74
-- title:
--   Coordinatewise exponent cutoffs bound weighted degree
-- statement:
--   If every exponent is strictly below its positive coordinate cutoff and all weights are positive, then the monomial’s weighted degree is no greater than the sum of the cutoff weights.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.weight_le_cutoff_of_lt
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (n : Fin d → Nat) (hn : ∀ i, 0 < n i)
    (e : Fin d →₀ Nat) (he : ∀ i : Fin d, e i < n i) :
    Finsupp.weight w e ≤ ∑ i : Fin d, ((n i : ℚ) - 1) * w i := by sorry
