-- Prove2me | Theorems.Thm_NoHair_timelike_reference_end_two_way_access
-- name    : NoHair.timelike_reference_end_two_way_access
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:39:07.004134+00:00
-- url     : https://prove2.me/theorems/5c4aa896-acf2-4f07-9592-bba3ac53ed88
-- title:
--   Every point of a stationary reference end with timelike generator communicates with arbitrarily distant regions
-- statement:
--   If the stationary Killing field is timelike everywhere on a chosen asymptotic reference end, then each point of the end can send and receive timelike signals to arbitrarily distant coordinate regions. The initial chart radius may be any radius for which the geometric timelikeness condition holds.
-- source:
--   P. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Section 2.2, pp. 6–7, equations (2.4)–(2.10) and the discussion of overlapping ends, https://arxiv.org/abs/0806.0016 . The numerical bound below is a sufficient estimate for the metric-component decay in the Prove2Me end chart.

import Definitions.Def_NoHair_chronologyAtInfinity

open NoHair Set
open scoped ContDiff Manifold BigOperators

theorem NoHair.timelike_reference_end_two_way_access {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ) (hg : IsLorentzian g) (hs : IsSmoothBilinField g)
    (T : VecField M) (hT : IsTimeOrientation g T) (hφ : IsSymmetryFlow g F φ)
    (hK : ∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0) :
    E.region ⊆ domainOfOuterCommunicationsAtInfinity g T (fun R => E.ψ '' exteriorRegion R) E.R := by
  sorry
