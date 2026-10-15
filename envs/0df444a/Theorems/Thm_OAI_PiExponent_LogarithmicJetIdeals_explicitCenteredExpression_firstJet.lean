-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_explicitCenteredExpression_firstJet
-- name    : OAI.PiExponent.LogarithmicJetIdeals.explicitCenteredExpression_firstJet
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:16:00.204159+00:00
-- url     : https://prove2.me/theorems/7ed31e70-2c35-455a-b917-6658970bd758
-- title:
--   First jet of the explicit centered series
-- statement:
--   The explicit series obtained from the coordinate expansion has zero constant terms and identity degree-one coefficients, since the lifted logarithm contributes exactly `X 0` to its linear part.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PowerSeries.Log

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.explicitCenteredExpression_firstJet
    {m : Nat} :
    (∀ i : Fin (m + 1), MvPowerSeries.coeff 0
      (if i = 0 then MvPowerSeries.X 0 else
        MvPowerSeries.X i + liftLogSeries m (PowerSeries.log Complex) - MvPowerSeries.X 0) = 0) ∧
    (∀ i j : Fin (m + 1), MvPowerSeries.coeff (Finsupp.single j 1)
      (if i = 0 then MvPowerSeries.X 0 else
        MvPowerSeries.X i + liftLogSeries m (PowerSeries.log Complex) - MvPowerSeries.X 0) =
        (if i = j then 1 else 0)) := by sorry
