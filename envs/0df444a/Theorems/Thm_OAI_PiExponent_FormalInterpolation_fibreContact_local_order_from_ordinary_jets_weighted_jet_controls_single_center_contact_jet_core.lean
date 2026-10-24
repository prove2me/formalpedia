-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_jet_core
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_jet_core
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:47:15.998086+00:00
-- url     : https://prove2.me/theorems/30e550dd-00a3-480c-bea5-5615fc578a02
-- title:
--   Weighted vanishing jets force a curve-order bound
-- statement:
--   For a nonnegative scalar C bounded by each powered coordinate contact, weighted Taylor coefficients vanishing strictly below H imply C·H is bounded by R times the evaluated polynomial’s nonnegative curve order. This isolates the weighted Taylor expansion and valuation estimate while retaining the exact strict cutoff and common scale.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_jet_core
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (v : Fin (m + 1) → Rat) (sigma : Rat)
    (hsigma : 0 < (sigma : Real))
    (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (x : Fin (m + 1) → E) (N : Nat) (hN : 0 < N)
    (f : MvPolynomial (Fin m) Complex)
    (hjet : fibreContactJetVanishing c (fun i => v i.succ)
      ((1 + 2 * (sigma : Real)) * (N : Real)) f)
    (nu : PolynomialCurvePlace E)
    (hne : MvPolynomial.aeval (fun i => x i.succ) f ≠ 0)
    (j : Fin K) (C : Real) (hC : 0 ≤ C)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (hcontact : ∀ i : Fin m, C ≤ (e i.succ : Real) *
      (polynomialCurveOrder nu
        (x i.succ - algebraMap Complex E (c j i)) : Real)) :
    C * ((1 + 2 * (sigma : Real)) * (N : Real)) ≤
      (R : Real) * max 0
        (polynomialCurveOrder nu (MvPolynomial.aeval (fun i => x i.succ) f) : Real) := by sorry
