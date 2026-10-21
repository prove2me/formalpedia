-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_log_linear_coefficients
-- name    : OAI.PiExponent.LogarithmicJetIdeals.log_linear_coefficients
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T17:46:26.727113+00:00
-- url     : https://prove2.me/theorems/5192c056-a78c-4d6e-b4de-7f90d67fb24f
-- title:
--   Constant and linear coefficients of the formal logarithm
-- statement:
--   The formal logarithm has constant coefficient zero and degree-one coefficient one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.log_linear_coefficients
    (n : Nat) (hn : n ≤ 1) :
    PowerSeries.coeff n (PowerSeries.log ℂ) = if n = 0 then 0 else 1 := by sorry
