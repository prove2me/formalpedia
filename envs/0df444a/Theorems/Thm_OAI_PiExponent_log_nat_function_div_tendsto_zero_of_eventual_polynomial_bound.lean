-- Prove2me | Theorems.Thm_OAI_PiExponent_log_nat_function_div_tendsto_zero_of_eventual_polynomial_bound
-- name    : OAI.PiExponent.log_nat_function_div_tendsto_zero_of_eventual_polynomial_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T23:09:41.979465+00:00
-- url     : https://prove2.me/theorems/20e91903-f9de-44f6-910a-9043af33c22f
-- title:
--   Logarithm of polynomially bounded natural-valued functions is sublinear
-- statement:
--   If an integer-valued function is eventually at least one and bounded above by a fixed polynomial in H+1, then its logarithm divided by H tends to zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Topology

theorem OAI.PiExponent.log_nat_function_div_tendsto_zero_of_eventual_polynomial_bound (f : ℝ → ℕ) (C : ℝ) (p : ℕ) (hC : 0 < C) (hbound : ∀ᶠ H : ℝ in atTop, 1 ≤ f H ∧ (f H : ℝ) ≤ C * (H + 1) ^ p) : Tendsto (fun H : ℝ => Real.log (f H : ℝ) / H) atTop (𝓝 0) := by sorry
