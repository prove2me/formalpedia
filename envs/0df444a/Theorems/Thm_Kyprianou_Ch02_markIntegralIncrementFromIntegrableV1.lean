-- Prove2me | Theorems.Thm_Kyprianou_Ch02_markIntegralIncrementFromIntegrableV1
-- name    : Kyprianou.Ch02.markIntegralIncrementFromIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:19:24.633749+00:00
-- url     : https://prove2.me/theorems/e190ab6b-425d-4727-af5a-cab0fe5468fb
-- title:
--   Cumulative marked integral increments equal integrals on the intervening time strip under local integrability
-- statement:
--   For any measure on ℝ×ℝ and a Borel mark set B, if the mark integrand z↦z.2 is integrable on (0,t]×B and 0≤s≤t, its cumulative integral has increment exactly equal to the integral over (s,t]×B. Proof partitions (0,t] as disjoint measurable union (0,s]∪(s,t] and applies the set-integral additivity lemma.
-- source:
--   Elementary Bochner set-integral additivity, Kyprianou (2006) Chapter 2

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.markIntegralIncrementFromIntegrableV1
    (μ : Measure (ℝ × ℝ)) (B : Set ℝ) (hB : MeasurableSet B)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hint : IntegrableOn (fun z : ℝ × ℝ => z.2) (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) μ) :
    (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂μ) -
    (∫ z in (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B), z.2 ∂μ) =
      ∫ z in (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ B), z.2 ∂μ := by sorry
