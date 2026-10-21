-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_X_zero_coeff_formula
-- name    : OAI.PiExponent.LogarithmicJetIdeals.X_zero_coeff_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T17:46:50.346533+00:00
-- url     : https://prove2.me/theorems/b66b0ba5-8227-41b0-9c74-6e92f6aefe69
-- title:
--   Coefficient formula for the first multivariate variable
-- statement:
--   The coefficient of the first multivariate variable is one exactly at its degree-one multi-index, and zero at every other multi-index.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.X_zero_coeff_formula
    {m : Nat} (d : Fin (m + 1) -> Nat) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
      (MvPowerSeries.X 0) =
      if (d 0 = 1 ∧ ∀ i : Fin (m + 1), i ≠ 0 → d i = 0) then 1 else 0 := by sorry
