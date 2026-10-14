-- Prove2me | Theorems.Thm_OAI_PiExponent_log_nat_polynomial_growth_div_tendsto
-- name    : OAI.PiExponent.log_nat_polynomial_growth_div_tendsto
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T15:31:54.928163+00:00
-- url     : https://prove2.me/theorems/b67b5917-ed03-469c-b415-3b31b476167e
-- title:
--   Logarithmic growth of polynomially bounded integer functions is sublinear
-- statement:
--   An eventually positive real parameter and an integer-valued function bounded between one and a fixed polynomial have logarithm divided by the parameter tending to zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticAggregate.lean#L74-L94

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed

open scoped Topology
open Filter

theorem OAI.PiExponent.log_nat_polynomial_growth_div_tendsto
    (f : ℝ → ℕ) (C : ℝ) (p : ℕ) (hC : 0 < C)
    (hbound : ∀ᶠ H : ℝ in atTop,
      0 < H ∧ 1 ≤ f H ∧ (f H : ℝ) ≤ C * H ^ p) :
    Tendsto (fun H : ℝ => Real.log (f H : ℝ) / H) atTop (𝓝 0) := by sorry
