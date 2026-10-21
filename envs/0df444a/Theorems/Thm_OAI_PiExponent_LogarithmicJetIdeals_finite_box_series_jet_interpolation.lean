-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_box_series_jet_interpolation
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finite_box_series_jet_interpolation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T05:25:42.998859+00:00
-- url     : https://prove2.me/theorems/56a4ac0f-f630-497f-943d-827ffcb057ec
-- title:
--   Finite-box interpolation for formal series at distinct centers
-- statement:
--   For finitely many requests at pairwise distinct centers, any prescribed local formal series at each center can be matched by one polynomial throughout each request's specified coordinatewise finite box.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.finite_box_series_jet_interpolation
    {iota alpha : Type} [Fintype alpha] [DecidableEq alpha] {m : Nat}
    (center : iota -> Fin m -> Complex) (slot : alpha -> iota)
    (degree : alpha -> Fin (m + 1) -> Nat)
    (hcenters : (i j : iota) -> Not (i = j) -> Exists fun k => Not (center i k = center j k))
    (S : iota -> MvPowerSeries (Fin (m + 1)) Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (b : alpha) -> (e : Fin (m + 1) -> Nat) ->
        ((k : Fin (m + 1)) -> LE.le (e k) (degree b k)) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet (center (slot b)) P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (S (slot b)) := by sorry
