-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_liftLogSeries_firstJet_coefficients
-- name    : OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_firstJet_coefficients
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T06:24:46.279832+00:00
-- url     : https://prove2.me/theorems/ff05e3d4-6af9-4c99-b657-8236ed796a81
-- title:
--   First coefficients of the lifted logarithm
-- statement:
--   The lifted logarithm has zero constant coefficient, and its degree-one coefficients are one in coordinate zero and zero in every other coordinate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PowerSeries.Log

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.liftLogSeries_firstJet_coefficients
    {m : Nat} :
    MvPowerSeries.coeff 0 (liftLogSeries m (PowerSeries.log Complex)) = 0 ∧
    (∀ j : Fin (m + 1),
      MvPowerSeries.coeff (Finsupp.single j 1)
        (liftLogSeries m (PowerSeries.log Complex)) = (if j = 0 then 1 else 0)) := by
  sorry
