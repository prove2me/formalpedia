-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_center_box_jet_interpolation
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finite_center_box_jet_interpolation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T05:38:43.589819+00:00
-- url     : https://prove2.me/theorems/17a80865-4cb5-4671-b3aa-995e1c5651e9
-- title:
--   Finite-box interpolation for formal jets at distinct centers
-- statement:
--   For any finite active family of pairwise distinct center vectors, every prescribed set of coefficients on a common rectangular finite box is realized by the formal jets of one polynomial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.finite_center_box_jet_interpolation
    {iota : Type} [DecidableEq iota] {m : Nat}
    (active : Finset iota)
    (center : iota -> Fin m -> Complex)
    (degree : Fin (m + 1) -> Nat)
    (hcenters : (i j : iota) -> Not (i = j) -> Exists fun k => Not (center i k = center j k))
    (value : iota -> (Fin (m + 1) -> Nat) -> Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (i : iota) -> i ∈ active ->
        (e : Fin (m + 1) -> Nat) ->
          ((k : Fin (m + 1)) -> e k <= degree k) ->
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (formalJet (center i) P) = value i e := by sorry
