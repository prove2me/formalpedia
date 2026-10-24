-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_generator_bound
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_generator_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:47:36.36519+00:00
-- url     : https://prove2.me/theorems/355f5cf4-a1ba-40b4-a061-e446b58c588c
-- title:
--   Logarithmic ideal contact is bounded by each coordinate generator
-- statement:
--   On the affine fibre x 0 = 1, each nonzero transverse logarithmic generator evaluates to x i.succ − c j i. Its e i.succ power belongs to the ideal, so its valuation bounds the ideal’s least finite contact. Transcendence ensures these translated coordinates are nonzero; the chart condition ensures their orders are nonnegative.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Mathlib.FieldTheory.IsAlgClosed.Basic

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_local_order_from_ordinary_jets_weighted_jet_controls_single_center_contact_generator_bound
    {m K : Nat} (c : Fin K → Fin m → Complex)
    (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (x : Fin (m + 1) → E) (hfibre : x 0 = 1)
    (hnonconst : ∀ i : Fin m, Transcendental Complex (x i.succ))
    (nu : PolynomialCurvePlace E)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (j : Fin K) :
    ∀ i : Fin m,
      (polynomialCurveIdealContact nu x
        (logarithmicCenterIdeal (c j) (fun _ => e 0) e) : Real) ≤
        (e i.succ : Real) *
          (polynomialCurveOrder nu
            (x i.succ - algebraMap Complex E (c j i)) : Real) := by sorry
