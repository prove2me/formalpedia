-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_jet_core_weighted_support_curve_bound
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_jet_core_weighted_support_curve_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:56:25.426993+00:00
-- url     : https://prove2.me/theorems/ff5c47b9-0304-41a4-85b0-42fc113270a5
-- title:
--   Weighted support controls curve order
-- statement:
--   If every monomial in P has weighted degree at least H, and each coordinate difference from the selected center has curve order at least C divided by its scale e_i, prove that the evaluation of P at those differences has order at least C·H/R, using R=e_i v_i. The nonzero original evaluation and its equality with the translated evaluation keep the order finite and identify the conclusion with the target.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.FieldTheory.IsAlgClosed.Basic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_jet_core_weighted_support_curve_bound
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
    (P : MvPolynomial (Fin m) Complex)
    (hsupport : ∀ a ∈ P.support,
      ((1 + 2 * (sigma : Real)) * (N : Real)) ≤
        ∑ i : Fin m, (a i : Real) * (v i.succ : Real))
    (nu : PolynomialCurvePlace E)
    (hne : MvPolynomial.aeval (fun i => x i.succ) f ≠ 0)
    (j : Fin K) (C : Real) (hC : 0 ≤ C)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (hcontact : ∀ i : Fin m, C ≤ (e i.succ : Real) *
      (polynomialCurveOrder nu
        (x i.succ - algebraMap Complex E (c j i)) : Real))
    (heval : MvPolynomial.aeval (fun i => x i.succ) f =
      MvPolynomial.aeval
        (fun i => x i.succ - algebraMap Complex E (c j i)) P) :
    C * ((1 + 2 * (sigma : Real)) * (N : Real)) ≤
      (R : Real) * max 0
        (polynomialCurveOrder nu (MvPolynomial.aeval (fun i => x i.succ) f) : Real) := by sorry
