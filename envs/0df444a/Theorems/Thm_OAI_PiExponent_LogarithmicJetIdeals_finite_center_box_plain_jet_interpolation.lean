-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_center_box_plain_jet_interpolation
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finite_center_box_plain_jet_interpolation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T05:45:28.785883+00:00
-- url     : https://prove2.me/theorems/d421156b-fe63-4b2f-93b6-abdfd31bc91f
-- title:
--   Finite-box affine jet interpolation at distinct centers
-- statement:
--   At a finite family of pairwise distinct centers, one polynomial realizes arbitrary coefficients of the affine Taylor expansions on a common finite rectangular box. This is multivariate Hermite interpolation at the points whose coordinates are 1 followed by the given center coordinates.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.finite_center_box_plain_jet_interpolation
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
            (OAI.PiExponent.LogarithmicJetIdeals.plainJet (center i) P) = value i e := by sorry
