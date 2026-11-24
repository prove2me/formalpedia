-- Prove2me | Theorems.Thm_Kyprianou_Ch02_realIntegralBindMeasurableV1
-- name    : Kyprianou.Ch02.realIntegralBindMeasurableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:38:59.758202+00:00
-- url     : https://prove2.me/theorems/17502dd3-5a24-4415-9e9e-9e56b6093112
-- title:
--   Real Bochner integral and integrability under a measurable measure bind
-- statement:
--   Extended integration for bind gives finiteness and equality for the absolute, positive and negative parts. Almost-sure absolute integrability and the real positive-minus-negative formula yield the stated result.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.9 and Exercise 2.6(ii); conditional mean of Poisson mark increments.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem realIntegralBindMeasurableV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℝ) (hM : Measurable M)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable f (P.bind M)) :
    (∀ᵐ ω ∂P, Integrable f (M ω)) ∧
      Integrable (fun ω => ∫ x, f x ∂(M ω)) P ∧
      (∫ ω, (∫ x, f x ∂(M ω)) ∂P) = ∫ x, f x ∂(P.bind M) := by sorry

end Kyprianou.Ch02
