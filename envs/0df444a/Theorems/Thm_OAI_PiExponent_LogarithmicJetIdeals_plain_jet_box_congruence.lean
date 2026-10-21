-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_plain_jet_box_congruence
-- name    : OAI.PiExponent.LogarithmicJetIdeals.plain_jet_box_congruence
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T05:58:53.023722+00:00
-- url     : https://prove2.me/theorems/8a9980a9-0b6f-449e-8239-070d70dcfa69
-- title:
--   Rectangular ideal congruence preserves box coefficients
-- statement:
--   Polynomials congruent modulo the rectangular affine jet ideal have equal plain-jet coefficients throughout the box, including its upper boundary.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_RectangularJetIdeal
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.plain_jet_box_congruence
    {m : Nat} (c : Fin m -> Complex) (degree : Fin (m + 1) -> Nat)
    (P Q : MvPolynomial (Fin (m + 1)) Complex)
    (h : P - Q ∈ OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeal c degree)
    (e : Fin (m + 1) -> Nat)
    (he : (k : Fin (m + 1)) -> e k <= degree k) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (OAI.PiExponent.LogarithmicJetIdeals.plainJet c P) =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (OAI.PiExponent.LogarithmicJetIdeals.plainJet c Q) := by sorry
