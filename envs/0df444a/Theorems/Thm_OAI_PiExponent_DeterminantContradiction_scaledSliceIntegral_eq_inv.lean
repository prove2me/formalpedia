-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_scaledSliceIntegral_eq_inv
-- name    : OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_eq_inv
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T02:25:45.405825+00:00
-- url     : https://prove2.me/theorems/fcb9ab49-e412-4aaa-a70b-158108f7f0fb
-- title:
--   Scaled slice density integral
-- statement:
--   The real value of the stated nonnegative integral is `1/(n+1)`. The integrand vanishes outside `[0,1]` and equals `(1-t)^n` there; the endpoint case `n = 0` gives the indicator of `[0,1]`, whose integral is `1`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib

open scoped BigOperators Topology

theorem OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_eq_inv (n : ℕ) :
    ENNReal.toReal (∫⁻ t : ℝ,
      (if 0 ≤ t ∧ t ≤ 1 then ENNReal.ofReal (1 - t) ^ n else 0)
      ∂MeasureTheory.volume) = (↑(n + 1 : ℕ) : ℝ)⁻¹ := by sorry
