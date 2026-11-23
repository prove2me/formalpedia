-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finiteIntensityRegionCutoffV1
-- name    : Kyprianou.Ch02.finiteIntensityRegionCutoffV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T07:52:21.546266+00:00
-- url     : https://prove2.me/theorems/cf0182bd-ecb0-48fb-a31c-d93b03520b19
-- title:
--   Finite-intensity cutoff preserves measurable disjoint regions
-- statement:
--   For any family of pairwise disjoint measurable sets in a measured space, replace each infinite-intensity set by the empty set. The resulting family remains measurable and pairwise disjoint, and every member has finite intensity. This supplies a finite-region family usable in the proved Poisson point-family independence theorem.
-- source:
--   Elementary measure and set theory, Chapter 2 of Kyprianou (2006); split from the existing Chapter 2 Poisson random measure countable-independence child 115918e3-0f06-4a8b-b139-8f88e933e165.

import Mathlib
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.finiteIntensityRegionCutoffV1
    {E ι : Type} [MeasurableSpace E] (m : Measure E) (A : ι → Set E)
    [DecidablePred (fun i => m (A i) < (⊤ : ENNReal))]
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    let B : ι → Set E := fun i => if m (A i) < ⊤ then A i else ∅
    (∀ i, MeasurableSet (B i)) ∧
    (∀ i, m (B i) < ⊤) ∧
    Pairwise (fun i j => Disjoint (B i) (B j)) := by sorry
