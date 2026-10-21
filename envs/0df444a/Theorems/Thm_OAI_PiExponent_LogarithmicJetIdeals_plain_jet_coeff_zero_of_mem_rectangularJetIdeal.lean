-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_plain_jet_coeff_zero_of_mem_rectangularJetIdeal
-- name    : OAI.PiExponent.LogarithmicJetIdeals.plain_jet_coeff_zero_of_mem_rectangularJetIdeal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:05:36.705562+00:00
-- url     : https://prove2.me/theorems/06981d31-383e-4f25-bf54-0a44dbcc97d9
-- title:
--   Box coefficients vanish on the rectangular jet ideal
-- statement:
--   Every coefficient indexed by an exponent in the rectangular box vanishes in the plain jet of a polynomial belonging to the rectangular jet ideal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_RectangularJetIdeal
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.plain_jet_coeff_zero_of_mem_rectangularJetIdeal
    {m : Nat} (c : Fin m -> Complex) (degree : Fin (m + 1) -> Nat)
    (R : MvPolynomial (Fin (m + 1)) Complex)
    (h : R ∈ OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeal c degree)
    (e : Fin (m + 1) -> Nat)
    (he : (k : Fin (m + 1)) -> e k <= degree k) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (OAI.PiExponent.LogarithmicJetIdeals.plainJet c R) = 0 := by sorry
