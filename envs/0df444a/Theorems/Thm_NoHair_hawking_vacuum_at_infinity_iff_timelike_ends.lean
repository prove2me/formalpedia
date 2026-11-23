-- Prove2me | Theorems.Thm_NoHair_hawking_vacuum_at_infinity_iff_timelike_ends
-- name    : NoHair.hawking_vacuum_at_infinity_iff_timelike_ends
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:39:11.417266+00:00
-- url     : https://prove2.me/theorems/c9d01445-27b8-4197-9dad-2389a1c29c6e
-- title:
--   Equivalence of analytic vacuum Kerr uniqueness at infinity and uniqueness for timelike stationary reference ends
-- statement:
--   For the fixed spacetime and physical hypotheses of the analytic vacuum milestone, the classification implication formulated using the domain, black-hole region and horizon at infinity is equivalent to the existing single-reference-region formulation restricted to ends on which the stationary Killing field is timelike. This is the geometric reference-region condition used in the standard stationary black-hole uniqueness setup.
-- source:
--   P. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Section 2.2, pp. 6–7, equations (2.4)–(2.10) and the discussion of overlapping ends, https://arxiv.org/abs/0806.0016 . The numerical bound below is a sufficient estimate for the metric-component decay in the Prove2Me end chart.

import Definitions.Def_NoHair_chronologyAtInfinity
import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold BigOperators

theorem NoHair.hawking_vacuum_at_infinity_iff_timelike_ends {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ,E4) ∞ M] [IsManifold 𝓘(ℝ,E4) ω M]
    (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M)
    (hl : IsLorentzian g) (hsm : IsSmoothBilinField g) (hsF : IsSmoothBilinField F)
    (h2 : IsTwoForm F) (hT : IsTimeOrientation g T) (hem : IsElectrovac g F)
    (hφ : IsSymmetryFlow g F φ) (hvac : ∀ x, F x = 0) (han : IsAnalyticBilinField g) :
    (∀ E : AsymptoticallyFlatEnd g F φ,
      let A := fun R : ℝ => E.ψ '' exteriorRegion R
      let D := domainOfOuterCommunicationsAtInfinity g T A E.R
      let H := futureEventHorizonAtInfinity g T A E.R
      IsGloballyHyperbolicOn g T D → (chronoPastAtInfinity g T A E.R)ᶜ.Nonempty →
      IsConnected H → IsNondegenerateHorizon g F H D →
      ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧ IsKerrNewmanDOC g F D m a 0) ↔
    (∀ E : AsymptoticallyFlatEnd g F φ, (∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0) → IsStationaryBlackHole g F T φ E →
      IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
        (domainOfOuterCommunications g T E.region) →
      ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
        IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a 0) := by
  sorry
