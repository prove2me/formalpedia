-- Prove2me | Theorems.Thm_NoHair_analytic_static_timelike_end_regular_slice
-- name    : NoHair.analytic_static_timelike_end_regular_slice
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T10:30:02.254815+00:00
-- url     : https://prove2.me/theorems/c565a43b-cd9f-426c-b0b5-f142152e2ec1
-- title:
--   A regular exterior static slice for the analytic vacuum problem with a timelike reference end
-- statement:
--   In the static branch of the analytic vacuum uniqueness problem, the geometric input sought is a single global slice covering the domain with the stationary time flow. The spatial metric and lapse extend regularly to a connected compact zero-lapse boundary, the lapse has nonzero derivative there, and the spatial chart has controlled asymptotic derivatives. Establishing these facts from the timelike end and the black-hole hypotheses would permit the existing conformal doubling argument to be used.
-- source:
--   G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of multiple black holes in asymptotically Euclidean static vacuum space-time, Gen. Relativ. Gravit. 19 (1987), 147–154, https://doi.org/10.1007/BF00770326. P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999), 661–687. Establishing the necessary global slice or completion for these precise mission hypotheses is part of the open obligation.

import Definitions.Def_NoHair_regularStaticVacuumSlice

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.analytic_static_timelike_end_regular_slice {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] [IsManifold 𝓘(ℝ, E4) ω M]
    (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (htime : ∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0)
    (hvac : ∀ x, F x = 0) (hanalytic : IsAnalyticBilinField g)
    (hnondeg : IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
      (domainOfOuterCommunications g T E.region))
    (hstatic : IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    HasRegularStaticVacuumSlice g φ (domainOfOuterCommunications g T E.region) := by
  sorry
