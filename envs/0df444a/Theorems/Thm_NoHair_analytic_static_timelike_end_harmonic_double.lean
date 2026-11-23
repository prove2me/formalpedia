-- Prove2me | Theorems.Thm_NoHair_analytic_static_timelike_end_harmonic_double
-- name    : NoHair.analytic_static_timelike_end_harmonic_double
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T09:59:59.764077+00:00
-- url     : https://prove2.me/theorems/51d6749e-ffad-440c-8e28-f8a291012ce5
-- title:
--   Conformal doubling of a static analytic vacuum exterior with a timelike reference end
-- statement:
--   Suppose the stationary field is hypersurface-orthogonal on the domain selected by a timelike stationary reference end in the revised analytic nondegenerate vacuum problem. The static geometric task is to construct the positive-lapse exterior chart of a Euclidean conformal double. Its conformal factor is nonnegative and harmonic away from the puncture, tends to one at infinity, and takes the horizon value two at a point away from the puncture. The chart must cover the entire domain of outer communications. Existence of a suitable regular static slice or a regular completion requires justification under the stated hypotheses.
-- source:
--   G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999), 661–687. Establishing the necessary global slice or completion for these precise mission hypotheses is part of the open obligation.

import Definitions.Def_NoHair_conformalVacuumExterior

open NoHair Set InnerProductSpace
open scoped ContDiff Manifold

theorem NoHair.analytic_static_timelike_end_harmonic_double {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] [IsManifold 𝓘(ℝ, E4) ω M]
    (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (htime : ∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0)
    (hvac : ∀ x, F x = 0) (hanalytic : IsAnalyticBilinField g)
    (hnondeg : IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
      (domainOfOuterCommunications g T E.region))
    (hstatic : IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ (U : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3)),
      HasConformalVacuumExterior g (domainOfOuterCommunications g T E.region) U ∧
      HarmonicOnNhd U ({0}ᶜ) ∧ (∀ x, x ≠ 0 → 0 ≤ U x) ∧
      (∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |U x - 1| ≤ ε) ∧ p ≠ 0 ∧ U p = 2 := by
  sorry
