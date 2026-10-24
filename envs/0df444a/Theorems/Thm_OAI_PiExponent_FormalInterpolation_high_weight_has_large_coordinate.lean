-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_high_weight_has_large_coordinate
-- name    : OAI.PiExponent.FormalInterpolation.high_weight_has_large_coordinate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T09:40:21.210169+00:00
-- url     : https://prove2.me/theorems/87203571-c79e-4eeb-ab57-348511ece5c7
-- title:
--   A high weight reaches a coordinate cutoff
-- statement:
--   If every coordinate weight is positive and the exponent vector's weighted sum strictly exceeds the sum of the coordinate cutoff weights, at least one exponent reaches its cutoff.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.high_weight_has_large_coordinate
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (n : Fin d → Nat) (hn : ∀ i, 0 < n i)
    (e : Fin d →₀ Nat)
    (hweight : (∑ i : Fin d, ((n i : ℚ) - 1) * w i) < Finsupp.weight w e) :
    ∃ i : Fin d, n i ≤ e i := by sorry
