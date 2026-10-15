-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_center_series_jet_patching
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finite_center_series_jet_patching
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T05:31:52.988477+00:00
-- url     : https://prove2.me/theorems/7f6eb1a0-5403-4bf3-95fd-c41b88a6ae9c
-- title:
--   Patching finite jets at distinct centers
-- statement:
--   For a finite set of centers with pairwise distinct center vectors, local polynomials that match prescribed series on a common finite box can be patched into one polynomial matching all those series on that box.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.finite_center_series_jet_patching
    {iota : Type} [DecidableEq iota] {m : Nat}
    (active : Finset iota)
    (center : iota -> Fin m -> Complex)
    (degree : Fin (m + 1) -> Nat)
    (hcenters : (i j : iota) -> Not (i = j) -> Exists fun k => Not (center i k = center j k))
    (S : iota -> MvPowerSeries (Fin (m + 1)) Complex)
    (Q : iota -> MvPolynomial (Fin (m + 1)) Complex)
    (hmatch : (i : iota) -> i ∈ active ->
      (e : Fin (m + 1) -> Nat) ->
        ((k : Fin (m + 1)) -> e k <= degree k) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet (center i) (Q i)) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (S i)) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (i : iota) -> i ∈ active ->
        (e : Fin (m + 1) -> Nat) ->
          ((k : Fin (m + 1)) -> e k <= degree k) ->
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (formalJet (center i) P) =
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (S i) := by sorry
