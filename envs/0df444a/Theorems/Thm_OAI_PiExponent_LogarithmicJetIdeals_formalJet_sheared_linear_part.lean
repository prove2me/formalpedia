-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_sheared_linear_part
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_sheared_linear_part
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T06:29:15.954986+00:00
-- url     : https://prove2.me/theorems/99364149-74cc-4e89-a613-b35f1e2c0790
-- title:
--   The sheared generator images preserve coefficients through degree one
-- statement:
--   For each generator image in the composed substitution, its constant and degree-one coefficients agree with those of the corresponding formal variable.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_sheared_linear_part
    {m : Nat} :
    ∀ (i : Fin (m + 1)) (d : Fin (m + 1) -> Nat),
      (∑ k : Fin (m + 1), d k) <= 1 ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (Fin.cases (MvPowerSeries.X 0)
            (fun j => MvPowerSeries.X j.succ +
              liftLogSeries m (PowerSeries.log ℂ) - MvPowerSeries.X 0) i) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (MvPowerSeries.X i) := by sorry
