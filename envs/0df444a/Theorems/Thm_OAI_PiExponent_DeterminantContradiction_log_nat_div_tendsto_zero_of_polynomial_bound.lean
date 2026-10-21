-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_log_nat_div_tendsto_zero_of_polynomial_bound
-- name    : OAI.PiExponent.DeterminantContradiction.log_nat_div_tendsto_zero_of_polynomial_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T23:13:45.232669+00:00
-- url     : https://prove2.me/theorems/10d03b67-e006-4ace-9a6b-f338fcbe30ea
-- title:
--   Logarithm of a polynomially bounded positive count is sublinear
-- statement:
--   Any eventually positive natural-valued function with an eventual polynomial upper bound has logarithm divided by its argument tending to zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology

theorem OAI.PiExponent.DeterminantContradiction.log_nat_div_tendsto_zero_of_polynomial_bound
    (f : ℝ → ℕ) (N : ℕ) (C : ℝ) (hC : 0 < C)
    (hpos : ∀ᶠ H : ℝ in atTop, 1 ≤ (f H : ℝ))
    (hbound : ∀ᶠ H : ℝ in atTop, (f H : ℝ) ≤ C * (H + 1) ^ N) :
    Tendsto (fun H : ℝ => Real.log (f H : ℝ) / H) atTop (𝓝 0) := by sorry
