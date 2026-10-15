-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_centeredCoordinate_firstJet
-- name    : OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate_firstJet
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:09:22.085585+00:00
-- url     : https://prove2.me/theorems/13686d15-e5e9-4078-8594-ae1111bd9a31
-- title:
--   Centered logarithmic coordinates have identity first jet
-- statement:
--   The formal logarithmic images of the centered polynomial coordinates have zero constant terms and identity linear coefficients.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_CenteredCoordinate
import Mathlib.RingTheory.MvPowerSeries.Equiv

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate_firstJet
    {m : Nat} (center : Fin m → Complex) :
    (∀ i, MvPowerSeries.coeff 0
      (formalJet center (OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate center i)) = 0) ∧
    (∀ i j, MvPowerSeries.coeff (Finsupp.single j 1)
      (formalJet center (OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate center i)) =
        (if i = j then 1 else 0)) := by sorry
