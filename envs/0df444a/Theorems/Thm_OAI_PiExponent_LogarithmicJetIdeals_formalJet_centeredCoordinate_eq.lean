-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_centeredCoordinate_eq
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_centeredCoordinate_eq
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:15:39.030534+00:00
-- url     : https://prove2.me/theorems/880387e3-fa80-43de-8b3c-a47ee94b2299
-- title:
--   Formal image of a centered coordinate
-- statement:
--   Evaluating a centered polynomial coordinate under the formal jet map yields `X 0` for coordinate zero, and `X i + liftLogSeries m (PowerSeries.log Complex) - X 0` for any other coordinate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_CenteredCoordinate
import Mathlib.RingTheory.MvPowerSeries.Equiv

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_centeredCoordinate_eq
    {m : Nat} (center : Fin m → Complex) (i : Fin (m + 1)) :
    formalJet center (OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate center i) =
      (if i = 0 then MvPowerSeries.X 0 else
        MvPowerSeries.X i + liftLogSeries m (PowerSeries.log Complex) - MvPowerSeries.X 0) := by sorry
