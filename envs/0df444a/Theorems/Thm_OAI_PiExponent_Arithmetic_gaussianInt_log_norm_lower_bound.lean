-- Prove2me | Theorems.Thm_OAI_PiExponent_Arithmetic_gaussianInt_log_norm_lower_bound
-- name    : OAI.PiExponent.Arithmetic.gaussianInt_log_norm_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T22:22:03.914031+00:00
-- url     : https://prove2.me/theorems/a2b74d4b-1bf7-4dd0-8894-d62b5a0a0a4a
-- title:
--   Logarithmic norm lower bound from a Gaussian integer certificate
-- statement:
--   If multiplying a nonzero complex number by a positive integer gives a Gaussian integer, the number’s logarithmic norm is at least the negative logarithm of that integer.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData

open scoped BigOperators

theorem OAI.PiExponent.Arithmetic.gaussianInt_log_norm_lower_bound
    {D : ℕ} {z : ℂ} (hD : 0 < D) (hz : z ≠ 0)
    (g : GaussianInt) (hg : (D : ℂ) * z = (g : ℂ)) :
    -Real.log (D : ℝ) ≤ Real.log ‖z‖ := by sorry
