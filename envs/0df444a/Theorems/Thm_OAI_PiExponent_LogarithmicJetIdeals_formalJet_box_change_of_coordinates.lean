-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_box_change_of_coordinates
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_box_change_of_coordinates
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T05:46:16.755989+00:00
-- url     : https://prove2.me/theorems/29b91425-54ab-4cbf-8108-06b5ef82ded1
-- title:
--   Finite jets under the logarithmic coordinate change
-- statement:
--   For arbitrary requested finite-box logarithmic jet values, there are compatible affine-jet values on the larger coordinatewise cube, such that any polynomial realizing those affine coefficients also realizes the requested logarithmic coefficients.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_box_change_of_coordinates
    {iota : Type} [DecidableEq iota] {m : Nat}
    (active : Finset iota)
    (center : iota -> Fin m -> Complex)
    (degree : Fin (m + 1) -> Nat)
    (value : iota -> (Fin (m + 1) -> Nat) -> Complex) :
    Exists fun standardValue : iota -> (Fin (m + 1) -> Nat) -> Complex =>
      (P : MvPolynomial (Fin (m + 1)) Complex) ->
        ((i : iota) -> i ∈ active ->
          (e : Fin (m + 1) -> Nat) ->
            ((k : Fin (m + 1)) -> e k <= ∑ j : Fin (m + 1), degree j) ->
            MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
              (OAI.PiExponent.LogarithmicJetIdeals.plainJet (center i) P) = standardValue i e) ->
        (i : iota) -> i ∈ active ->
          (e : Fin (m + 1) -> Nat) ->
            ((k : Fin (m + 1)) -> e k <= degree k) ->
            MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
              (formalJet (center i) P) = value i e := by sorry
