-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_bounds_tendsto
-- name    : OAI.PiExponent.DeterminantContradiction.weightedSimplex_bounds_tendsto
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:34:49.131864+00:00
-- url     : https://prove2.me/theorems/e188901c-2e86-4554-8218-3826f3a79b16
-- title:
--   Shifted weighted simplex volume bounds have the same normalized limit
-- statement:
--   For fixed dimension and strictly positive weights, both shifted simplex-volume bounds, divided by H^n, tend to the reciprocal of n! times the product of the weights. This follows from the leading coefficient of the shifted degree-n powers and includes n = 0.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real.Lemmas
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.weightedSimplex_bounds_tendsto
    (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    Tendsto (fun H : ℝ =>
      (H - ∑ i, w i) ^ n / ((n.factorial : ℝ) * ∏ i, w i) / H ^ n)
      atTop (nhds (1 / ((n.factorial : ℝ) * ∏ i, w i))) ∧
    Tendsto (fun H : ℝ =>
      (H + ∑ i, w i) ^ n / ((n.factorial : ℝ) * ∏ i, w i) / H ^ n)
      atTop (nhds (1 / ((n.factorial : ℝ) * ∏ i, w i))) := by sorry
