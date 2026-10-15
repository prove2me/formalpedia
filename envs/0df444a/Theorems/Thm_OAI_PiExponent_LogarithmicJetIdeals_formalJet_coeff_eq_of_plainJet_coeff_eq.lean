-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coeff_eq_of_plainJet_coeff_eq
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_eq_of_plainJet_coeff_eq
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T05:53:54.157786+00:00
-- url     : https://prove2.me/theorems/5cb3cbd0-61f8-4cf2-bbc5-d5d4e8fbae1b
-- title:
--   Finite coefficient dependence under the logarithmic change
-- statement:
--   If two polynomials have equal plain-jet coefficients throughout the cube bounded by the sum of the requested degrees, then their logarithmic-jet coefficients agree on the requested coordinatewise box.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_coeff_eq_of_plainJet_coeff_eq
    {m : Nat}
    (center : Fin m -> Complex)
    (degree : Fin (m + 1) -> Nat)
    (P Q : MvPolynomial (Fin (m + 1)) Complex)
    (hPQ : (e : Fin (m + 1) -> Nat) ->
      ((k : Fin (m + 1)) -> e k <= ∑ j : Fin (m + 1), degree j) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (OAI.PiExponent.LogarithmicJetIdeals.plainJet center P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (OAI.PiExponent.LogarithmicJetIdeals.plainJet center Q)) :
    (e : Fin (m + 1) -> Nat) ->
      ((k : Fin (m + 1)) -> e k <= degree k) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center Q) := by sorry
