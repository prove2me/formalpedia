-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_product_law_integral_nested_sfinite
-- name    : NestedSeatAlloc.IntPolicy.product_law_integral_nested_sfinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T13:51:36.64205+00:00
-- url     : https://prove2.me/theorems/3cd51073-85e7-4424-970c-9397e1412b16
-- title:
--   Product-law iterated integral with explicit s-finite marginals
-- statement:
--   # Corrected product-law integration lemma with s-finite marginals
--
--   The first proposed generic theorem, product_law_integral_nested
--   (ID 42ecae3d-b274-48e0-9e20-3f7a3775b374), was missing essential
--   s-finiteness assumptions. Its submitted Lean proof returned a typeclass
--   failure: no SFinite instance for Measure.map U P, required by
--   MeasureTheory.integral_prod. A generic product law and Integrable F do
--   not by themselves furnish the s-finite instances needed by Fubini.
--   Do not mark the first theorem Proved or retry an identical proof.
--
--   This corrected version explicitly requires
--   SFinite (Measure.map U P) and SFinite (Measure.map Z P).
--   The proof introduces both instances and then uses measurable
--   pushforward (integral_map), the assumed joint product law,
--   and integral_prod. These are the exact three steps of the source
--   proof, now with the necessary hypotheses made visible.
--
--   In the seat-allocation model P is a probability measure and U,Z are
--   measurable, so their marginal maps are probability measures and
--   therefore s-finite. Proving those instances is a separate easy
--   obligation in the model-specific theorem, not an assumption to hide.
--
--   No local Lean or Lake compilation has been run.
-- source:
--   # Corrected product-law integration lemma with s-finite marginals
--
--   The first proposed generic theorem, product_law_integral_nested
--   (ID 42ecae3d-b274-48e0-9e20-3f7a3775b374), was missing essential
--   s-finiteness assumptions. Its submitted Lean proof returned a typeclass
--   failure: no SFinite instance for Measure.map U P, required by
--   MeasureTheory.integral_prod. A generic product law and Integrable F do
--   not by themselves furnish the s-finite instances needed by Fubini.
--   Do not mark the first theorem Proved or retry an identical proof.
--
--   This corrected version explicitly requires
--   SFinite (Measure.map U P) and SFinite (Measure.map Z P).
--   The proof introduces both instances and then uses measurable
--   pushforward (integral_map), the assumed joint product law,
--   and integral_prod. These are the exact three steps of the source
--   proof, now with the necessary hypotheses made visible.
--
--   In the seat-allocation model P is a probability measure and U,Z are
--   measurable, so their marginal maps are probability measures and
--   therefore s-finite. Proving those instances is a separate easy
--   obligation in the model-specific theorem, not an assumption to hide.
--
--   No local Lean or Lake compilation has been run.

import Mathlib
open MeasureTheory ProbabilityTheory

theorem NestedSeatAlloc.IntPolicy.product_law_integral_nested_sfinite {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) (U : Ω → α) (Z : Ω → β)
    (hU : Measurable U) (hZ : Measurable Z)
    (hsU : SFinite (Measure.map U P))
    (hsZ : SFinite (Measure.map Z P))
    (F : β × α → ℝ) (hF : Measurable F)
    (hjoint : Measure.map (fun ω => (Z ω, U ω)) P =
      (Measure.map Z P).prod (Measure.map U P))
    (hInt : Integrable F ((Measure.map Z P).prod (Measure.map U P))) :
    (∫ ω, F (Z ω, U ω) ∂P) =
      ∫ z, ∫ u, F (z, u) ∂(Measure.map U P) ∂(Measure.map Z P) := by sorry
