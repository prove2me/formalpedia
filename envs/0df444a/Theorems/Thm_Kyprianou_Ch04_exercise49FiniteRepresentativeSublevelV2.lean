-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49FiniteRepresentativeSublevelV2
-- name    : Kyprianou.Ch04.exercise49FiniteRepresentativeSublevelV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:31:58.143347+00:00
-- url     : https://prove2.me/theorems/a5370b20-9686-40b4-bef2-69d8da5cd96f
-- title:
--   Pointwise measurable finite representative implies measurable sublevels
-- statement:
--   Pointwise measurable finite representative implies measurable sublevels
-- source:
--   Kyprianou (2006), Chapter 4, Exercises 4.1 and 4.9.

import Mathlib

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49FiniteRepresentativeSublevelV2 {Ω : Type} [MeasurableSpace Ω]
    (τ : Ω → WithTop NNReal) (E : Set Ω) (hE : MeasurableSet E)
    (hfin : ∀ ω ∈ E, τ ω ≠ ⊤)
    (f : Ω → NNReal) (hf : Measurable f)
    (heq : ∀ ω, τ ω ≠ ⊤ → τ ω = (f ω : WithTop NNReal))
    (a : NNReal) :
    MeasurableSet (E ∩ {ω | τ ω ≤ (a : WithTop NNReal)})  := by
  sorry
