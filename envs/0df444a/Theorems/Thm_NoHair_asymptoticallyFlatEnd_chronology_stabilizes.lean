-- Prove2me | Theorems.Thm_NoHair_asymptoticallyFlatEnd_chronology_stabilizes
-- name    : NoHair.asymptoticallyFlatEnd_chronology_stabilizes
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:20:50.86627+00:00
-- url     : https://prove2.me/theorems/736b1f05-4a9d-4288-b037-93468ae85143
-- title:
--   The domain of outer communications at infinity is realized by every sufficiently distant coordinate cutoff
-- statement:
--   Let $A_R=\psi(\{\rho>R\})$ be the regions of an asymptotically flat end in any smooth time-oriented Lorentzian spacetime. For every $R_0\ge\max(R_E,16|C|)$, the chronological past and future of the single reference region $A_{R_0}$ agree with the corresponding sets defined by communication with arbitrarily distant regions. The ordinary domain of outer communications and future horizon computed at $R_0$ therefore agree with their cutoff-independent counterparts. The field equations, black-hole classification and Kerr coordinates are unnecessary for this conclusion.
-- source:
--   P. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Section 2.2, pp. 6–7, equations (2.4)–(2.10) and the discussion of overlapping ends, https://arxiv.org/abs/0806.0016 . The numerical bound below is a sufficient estimate for the metric-component decay in the Prove2Me end chart.

import Definitions.Def_NoHair_chronologyAtInfinity

open NoHair Set
open scoped ContDiff Manifold BigOperators

theorem NoHair.asymptoticallyFlatEnd_chronology_stabilizes {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ)
    (hg : IsLorentzian g) (hs : IsSmoothBilinField g) (T : VecField M) (hT : IsTimeOrientation g T)
    (R₀ : ℝ) (hR : E.R ≤ R₀) (hC : 16 * |E.C| ≤ R₀) :
    let A := fun R : ℝ => E.ψ '' exteriorRegion R
    chronoPastAtInfinity g T A E.R = chronoPastSet g T (A R₀) ∧
    chronoFutureAtInfinity g T A E.R = chronoFutureSet g T (A R₀) ∧
    domainOfOuterCommunicationsAtInfinity g T A E.R = domainOfOuterCommunications g T (A R₀) ∧
    futureEventHorizonAtInfinity g T A E.R = futureEventHorizon g T (A R₀) := by
  sorry
