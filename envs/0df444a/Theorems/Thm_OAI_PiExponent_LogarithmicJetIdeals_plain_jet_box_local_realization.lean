-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_plain_jet_box_local_realization
-- name    : OAI.PiExponent.LogarithmicJetIdeals.plain_jet_box_local_realization
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T05:58:20.950974+00:00
-- url     : https://prove2.me/theorems/544c28c2-82f7-42e3-bb57-9490baba41a7
-- title:
--   Local realization of a rectangular affine jet
-- statement:
--   At one affine center, a polynomial realizes arbitrary prescribed coefficients on any finite rectangular box, including boxes with zero cutoffs.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.plain_jet_box_local_realization
    {m : Nat} (c : Fin m -> Complex) (degree : Fin (m + 1) -> Nat)
    (value : (Fin (m + 1) -> Nat) -> Complex) :
    Exists fun Q : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        ((k : Fin (m + 1)) -> e k <= degree k) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (OAI.PiExponent.LogarithmicJetIdeals.plainJet c Q) = value e := by sorry
