-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_box_jet_gluing
-- name    : OAI.PiExponent.LogarithmicJetIdeals.box_jet_gluing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T05:19:13.686989+00:00
-- url     : https://prove2.me/theorems/ebb0d236-56f8-49e0-a7d5-2a756144eecb
-- title:
--   Finite box-jet gluing at distinct centers
-- statement:
--   Given finitely many requests at pairwise distinct centers, one polynomial matches every formal-jet coefficient in each requested coordinatewise box, with the prescribed coefficients taken from the local polynomial associated to that request's slot.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.box_jet_gluing
    {iota alpha : Type} [Fintype alpha] [DecidableEq alpha] {m : Nat}
    (center : iota -> Fin m -> Complex) (slot : alpha -> iota)
    (degree : alpha -> Fin (m + 1) -> Nat)
    (hcenters : (i j : iota) -> Not (i = j) -> Exists fun k => Not (center i k = center j k))
    (Q : iota -> MvPolynomial (Fin (m + 1)) Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (b : alpha) -> (e : Fin (m + 1) -> Nat) ->
        ((k : Fin (m + 1)) -> LE.le (e k) (degree b k)) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet (center (slot b)) P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet (center (slot b)) (Q (slot b))) := by sorry
