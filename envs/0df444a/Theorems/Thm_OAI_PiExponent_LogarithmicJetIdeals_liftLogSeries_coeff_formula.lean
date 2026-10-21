-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_liftLogSeries_coeff_formula
-- name    : OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_coeff_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T17:45:45.090392+00:00
-- url     : https://prove2.me/theorems/b709beef-da67-4de1-9365-dc842e1a6460
-- title:
--   Coefficient formula for the lifted univariate series
-- statement:
--   A coefficient of the lifted series vanishes when some coordinate other than coordinate zero has positive degree; otherwise it is the univariate coefficient at the degree of coordinate zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_coeff_formula
    {m : Nat} (d : Fin (m + 1) -> Nat) (f : PowerSeries ℂ) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
      (liftLogSeries m f) =
      if (∀ i : Fin (m + 1), i ≠ 0 → d i = 0) then
        PowerSeries.coeff (d 0) f else 0 := by sorry
