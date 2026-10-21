-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_liftLogSeries_linear_coeff
-- name    : OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_linear_coeff
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T17:35:54.232984+00:00
-- url     : https://prove2.me/theorems/0b30eac7-401c-41d3-bb4f-369e74b4637f
-- title:
--   The lifted logarithm agrees with the first coordinate through degree one
-- statement:
--   For each multi-index of total degree at most one, the lifted logarithm has the same coefficient as the first formal variable.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_linear_coeff
    {m : Nat} (d : Fin (m + 1) -> Nat)
    (hd : (∑ k : Fin (m + 1), d k) <= 1) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
      (liftLogSeries m (PowerSeries.log ℂ)) =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
      (MvPowerSeries.X 0) := by sorry
