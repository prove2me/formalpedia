-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_product_law_integral_nested
-- name    : NestedSeatAlloc.IntPolicy.product_law_integral_nested
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T13:42:27.206505+00:00
-- url     : https://prove2.me/theorems/42ecae3d-b274-48e0-9e20-3f7a3775b374
-- title:
--   Push-forward product law converts nested demand expectation into an iterated integral
-- statement:
--   # Product-law integration bridge for independent nested demands
--
--   This generic lemma converts an expectation over a sample space into an
--   iterated integral over the marginal laws of a pair of measurable random
--   variables Z (new fare-class demand) and U (the complete higher-fare demand
--   prefix). The assumption hjoint is the exact push-forward/product-law
--   identity that follows from IndepFun Z U P. The integrability assumption
--   hInt is formulated on the product measure, which matches the exact
--   source signature of MeasureTheory.integral_prod in the pinned Mathlib
--   revision.
--
--   Proof: use integral_map to push the integral through the measurable
--   joint map ω↦(Z ω,U ω); rewrite the resulting joint distribution by
--   hjoint; apply integral_prod to integrate first over U then over Z.
--
--   For the published target expRevenue_eq_integral_condRevenue,
--   instantiate Z = X(k+1), U = the vector of X(1),...,X(k). Derive
--   hjoint from iIndepFun, construct a reconstruction function from the
--   vector to a full demand path, and use the Proved
--   condRevenue_eq_integral_prefix_law to identify the inner integral.
--
--   The product integrability assumption must be proved from the existing
--   revenue_integrable_of_seat_model, integrability of the pushed-forward
--   revenue, and hjoint. This is a genuine additional proof obligation;
--   no application of the lemma should silently assume it.
--
--   Source header checked at pinned Mathlib revision:
--   - MeasureTheory.integral_map:
--     ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ.
--   - MeasureTheory.integral_prod:
--     ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x,y) ∂ν ∂μ.
--   No local Lean or Lake has been run; the formal proof needs remote validation.
-- source:
--   # Product-law integration bridge for independent nested demands
--
--   This generic lemma converts an expectation over a sample space into an
--   iterated integral over the marginal laws of a pair of measurable random
--   variables Z (new fare-class demand) and U (the complete higher-fare demand
--   prefix). The assumption hjoint is the exact push-forward/product-law
--   identity that follows from IndepFun Z U P. The integrability assumption
--   hInt is formulated on the product measure, which matches the exact
--   source signature of MeasureTheory.integral_prod in the pinned Mathlib
--   revision.
--
--   Proof: use integral_map to push the integral through the measurable
--   joint map ω↦(Z ω,U ω); rewrite the resulting joint distribution by
--   hjoint; apply integral_prod to integrate first over U then over Z.
--
--   For the published target expRevenue_eq_integral_condRevenue,
--   instantiate Z = X(k+1), U = the vector of X(1),...,X(k). Derive
--   hjoint from iIndepFun, construct a reconstruction function from the
--   vector to a full demand path, and use the Proved
--   condRevenue_eq_integral_prefix_law to identify the inner integral.
--
--   The product integrability assumption must be proved from the existing
--   revenue_integrable_of_seat_model, integrability of the pushed-forward
--   revenue, and hjoint. This is a genuine additional proof obligation;
--   no application of the lemma should silently assume it.
--
--   Source header checked at pinned Mathlib revision:
--   - MeasureTheory.integral_map:
--     ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ.
--   - MeasureTheory.integral_prod:
--     ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x,y) ∂ν ∂μ.
--   No local Lean or Lake has been run; the formal proof needs remote validation.

import Mathlib
open MeasureTheory ProbabilityTheory

theorem NestedSeatAlloc.IntPolicy.product_law_integral_nested {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) (U : Ω → α) (Z : Ω → β)
    (hU : Measurable U) (hZ : Measurable Z)
    (F : β × α → ℝ) (hF : Measurable F)
    (hjoint : Measure.map (fun ω => (Z ω, U ω)) P =
      (Measure.map Z P).prod (Measure.map U P))
    (hInt : Integrable F ((Measure.map Z P).prod (Measure.map U P))) :
    (∫ ω, F (Z ω, U ω) ∂P) =
      ∫ z, ∫ u, F (z, u) ∂(Measure.map U P) ∂(Measure.map Z P) := by sorry
