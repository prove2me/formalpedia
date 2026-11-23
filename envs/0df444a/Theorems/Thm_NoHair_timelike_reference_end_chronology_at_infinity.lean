-- Prove2me | Theorems.Thm_NoHair_timelike_reference_end_chronology_at_infinity
-- name    : NoHair.timelike_reference_end_chronology_at_infinity
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:39:13.787225+00:00
-- url     : https://prove2.me/theorems/dd7f25e8-63c7-4bcd-bb0a-91cbc7b84b08
-- title:
--   A timelike stationary reference end gives the domain of outer communications and future horizon at infinity
-- statement:
--   When the stationary Killing field is timelike on the whole chosen reference end, its chronological past and future equal those defined by communication with all arbitrarily distant coordinate regions of the end. Its domain of outer communications and its future horizon therefore agree with the corresponding sets at infinity. The formulation uses only a geometric condition on the reference region.
-- source:
--   P. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Section 2.2, pp. 6–7, equations (2.4)–(2.10) and the discussion of overlapping ends, https://arxiv.org/abs/0806.0016 . The numerical bound below is a sufficient estimate for the metric-component decay in the Prove2Me end chart.

import Definitions.Def_NoHair_chronologyAtInfinity

open NoHair Set
open scoped ContDiff Manifold BigOperators

theorem NoHair.timelike_reference_end_chronology_at_infinity {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ) (hg : IsLorentzian g) (hs : IsSmoothBilinField g)
    (T : VecField M) (hT : IsTimeOrientation g T) (hφ : IsSymmetryFlow g F φ)
    (hK : ∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0) :
    let A := fun R => E.ψ '' exteriorRegion R
    chronoPastAtInfinity g T A E.R = chronoPastSet g T E.region ∧
    chronoFutureAtInfinity g T A E.R = chronoFutureSet g T E.region ∧
    domainOfOuterCommunicationsAtInfinity g T A E.R = domainOfOuterCommunications g T E.region ∧
    futureEventHorizonAtInfinity g T A E.R = futureEventHorizon g T E.region := by
  sorry
