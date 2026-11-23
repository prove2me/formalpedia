-- Prove2me | Theorems.Thm_NoHair_hawking_vacuum_at_infinity_iff_distant_ends
-- name    : NoHair.hawking_vacuum_at_infinity_iff_distant_ends
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T09:28:51.587686+00:00
-- url     : https://prove2.me/theorems/2d074be2-e378-444d-a6fc-f8dcd141ab77
-- title:
--   Equivalence of the at-infinity and distant-end formulations of analytic vacuum Kerr uniqueness
-- statement:
--   Fix the analytic vacuum spacetime, time orientation and stationary symmetry flow of the Hawking–Carter–Robinson milestone. Consider the uniqueness implication for all its asymptotically flat ends. Computing global hyperbolicity, the black-hole region, the connected nondegenerate horizon and the Kerr isometry conclusion from communication with arbitrarily far regions is equivalent to using the existing single-region predicates on ends satisfying $16|C|\le R_E$. Here $C$ is the decay constant recorded by the end. A classification proof for either formulation supplies one for the other.
-- source:
--   P. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Section 2.2, pp. 6–7, equations (2.4)–(2.10) and the discussion of overlapping ends, https://arxiv.org/abs/0806.0016 . The numerical bound below is a sufficient estimate for the metric-component decay in the Prove2Me end chart.

import Definitions.Def_NoHair_chronologyAtInfinity
import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold BigOperators

theorem NoHair.hawking_vacuum_at_infinity_iff_distant_ends {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
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
    (∀ E : AsymptoticallyFlatEnd g F φ, 16 * |E.C| ≤ E.R → IsStationaryBlackHole g F T φ E →
      IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
        (domainOfOuterCommunications g T E.region) →
      ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
        IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a 0) := by
  sorry
