-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sigmaFiniteDisjointExhaustion
-- name    : Kyprianou.Ch02.sigmaFiniteDisjointExhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:35:19.9082+00:00
-- url     : https://prove2.me/theorems/4b400af8-dd6a-4fe5-a738-17b001d679dc
-- title:
--   A sigma-finite intensity has a measurable disjoint finite-mass exhaustion
-- statement:
--   For a sigma-finite measure, the disjointed spanning sets form a countable pairwise-disjoint measurable covering by sets of finite measure. This is the first step of the source proof of Poisson random measure existence.
-- source:
--   LevyStochCalc/Poisson/RandomMeasure.lean, sigmaFinite_decomposition, source proof of Kyprianou Chapter 2 Theorem 2.4

import Mathlib
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

universe u
namespace Kyprianou.Ch02
theorem sigmaFiniteDisjointExhaustion
    (E : Type u) [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] :
    ∃ s : ℕ → Set E,
      (∀ n, MeasurableSet (s n)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) ∧
      (∀ n, ν (s n) < ⊤) ∧
      (⋃ n, s n) = Set.univ := by sorry
end Kyprianou.Ch02
