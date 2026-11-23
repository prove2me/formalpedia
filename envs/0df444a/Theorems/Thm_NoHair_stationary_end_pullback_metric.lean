-- Prove2me | Theorems.Thm_NoHair_stationary_end_pullback_metric
-- name    : NoHair.stationary_end_pullback_metric
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:39:03.377511+00:00
-- url     : https://prove2.me/theorems/a62f8b3b-e4da-4c66-960c-9cf746f25897
-- title:
--   The pullback metric is continuous and invariant under time translation in a stationary end chart
-- statement:
--   In the asymptotic chart of a smooth stationary spacetime the pullback metric depends continuously on its base point and two tangent vectors. Each coordinate time translation preserves this bilinear form, and the coordinate time vector pushes forward to the stationary Killing field.
-- source:
--   P. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Section 2.2, pp. 6–7, equations (2.4)–(2.10) and the discussion of overlapping ends, https://arxiv.org/abs/0806.0016 . The numerical bound below is a sufficient estimate for the metric-component decay in the Prove2Me end chart.

import Definitions.Def_NoHair_spacetime

open NoHair Set
open scoped ContDiff Manifold BigOperators

theorem NoHair.stationary_end_pullback_metric {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ) (hs : IsSmoothBilinField g) (hφ : IsSymmetryFlow g F φ) :
    let L := fun y => mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) E.ψ y
    let B := fun (y v w : E4) => g (E.ψ y) (L y v) (L y w)
    ContinuousOn (fun z : E4 × (E4 × E4) => B z.1 z.2.1 z.2.2) (exteriorRegion E.R ×ˢ Set.univ) ∧
    (∀ y ∈ exteriorRegion E.R, ∀ (s : ℝ) (v w : E4), B (y+s • coordBasis 0) v w = B y v w) ∧
    ∀ y ∈ exteriorRegion E.R, flowGenerator φ (E.ψ y) = L y (coordBasis 0) := by
  sorry
