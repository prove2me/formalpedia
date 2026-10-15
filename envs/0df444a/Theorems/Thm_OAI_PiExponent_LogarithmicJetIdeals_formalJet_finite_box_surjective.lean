-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_finite_box_surjective
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_finite_box_surjective
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T05:53:18.255152+00:00
-- url     : https://prove2.me/theorems/d7836aee-9c37-4059-b40f-dbf561ed8da9
-- title:
--   Surjectivity of finite logarithmic jet coordinates
-- statement:
--   For any center, finite coordinatewise degree box, and prescribed complex coefficients on that box, a polynomial has those coefficients after the logarithmic jet substitution.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_finite_box_surjective
    {m : Nat}
    (center : Fin m -> Complex)
    (degree : Fin (m + 1) -> Nat)
    (value : (Fin (m + 1) -> Nat) -> Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        ((k : Fin (m + 1)) -> e k <= degree k) ->
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (formalJet center P) = value e := by sorry
