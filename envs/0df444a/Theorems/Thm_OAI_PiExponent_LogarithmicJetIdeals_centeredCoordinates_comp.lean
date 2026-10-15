-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_centeredCoordinates_comp
-- name    : OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinates_comp
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:09:58.562132+00:00
-- url     : https://prove2.me/theorems/0d51ed37-2305-4a26-ab61-d863ea3431fb
-- title:
--   Formal jet respects polynomial composition in centered coordinates
-- statement:
--   Taking the formal jet commutes with evaluating a polynomial in the centered polynomial coordinates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_CenteredCoordinate
import Mathlib.RingTheory.MvPowerSeries.Equiv

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinates_comp
    {m : Nat} (center : Fin m → Complex)
    (Q : MvPolynomial (Fin (m + 1)) Complex) :
    formalJet center
        (MvPolynomial.aeval
          (OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate center) Q) =
      MvPolynomial.aeval
        (fun i => formalJet center
          (OAI.PiExponent.LogarithmicJetIdeals.centeredCoordinate center i)) Q := by sorry
