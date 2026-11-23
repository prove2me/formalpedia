-- Prove2me | Theorems.Thm_NoHair_hawking_analytic_nondegenerate_vacuum_timelike_end
-- name    : NoHair.hawking_analytic_nondegenerate_vacuum_timelike_end
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T09:59:56.079045+00:00
-- url     : https://prove2.me/theorems/b726bbbf-8b33-4728-8c26-2a45b08e738d
-- title:
--   Analytic nondegenerate vacuum Kerr uniqueness with a timelike stationary reference end
-- statement:
--   Let the spacetime be a stationary analytic vacuum black hole with a connected nondegenerate future horizon and globally hyperbolic domain of outer communications as in the Hawking–Carter–Robinson milestone. Require the stationary Killing field to be timelike at every point of the chosen asymptotically flat reference region. The proposed classification states that the entire domain is isometric to the vacuum Kerr exterior for some $m>0$ and $a^2\le m^2$. This is a candidate revision of the disproved milestone. The additional geometric condition eliminates its inner-horizon counterexample and agrees with computing the causal sets from communication with arbitrarily distant regions.
-- source:
--   P. T. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Astérisque 321 (2008), Definition 1.1, Theorem 1.3, §2.2 and §§6–7, https://arxiv.org/abs/0806.0016. The classical theorem assumes I⁺-regularity. The proposed single-hypothesis revision of the mission statement is an open problem.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.hawking_analytic_nondegenerate_vacuum_timelike_end {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] [IsManifold 𝓘(ℝ, E4) ω M]
    (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (htime : ∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0)
    (hvac : ∀ x, F x = 0) (hanalytic : IsAnalyticBilinField g)
    (hnondeg : IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
      (domainOfOuterCommunications g T E.region)) :
    ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
      IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a 0 := by
  sorry
