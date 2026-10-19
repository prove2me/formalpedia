-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_coord_zero_lt_of_weight_lt
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coord_zero_lt_of_weight_lt
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T07:18:53.405229+00:00
-- url     : https://prove2.me/theorems/791aa33c-0858-47be-8522-0392e7fe98ce
-- title:
--   A supported exponent below the replacement weight has low degree
-- statement:
--   For an exponent supported on coordinate zero, strict weighted degree below `u i`, together with `0 < v0` and `u i ≤ N i * v0`, forces its coordinate-zero degree to be strictly below `N i`. The statement retains the strict inequality and positivity needed for the cancellation, including the zero-cutoff boundary.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_coord_zero_lt_of_weight_lt
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (N : Fin m → ℕ)
    (hv0 : 0 < v0)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (i : Fin m) (α : Fin (m + 1) →₀ ℕ)
    (htail : ∀ j : Fin m, α j.succ = 0)
    (hα : (∑ j, Fin.cases v0 u j * (α j : ℝ)) < u i) :
    α 0 < N i := by sorry
