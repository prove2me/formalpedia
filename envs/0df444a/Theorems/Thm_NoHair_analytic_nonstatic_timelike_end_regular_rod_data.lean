-- Prove2me | Theorems.Thm_NoHair_analytic_nonstatic_timelike_end_regular_rod_data
-- name    : NoHair.analytic_nonstatic_timelike_end_regular_rod_data
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T10:33:45.736276+00:00
-- url     : https://prove2.me/theorems/faae5ba7-022c-4032-b920-4c1f6d14285b
-- title:
--   Weyl coordinates and regular axis and horizon endpoint data for a nonstatic timelike-end exterior
-- statement:
--   The geometric task in a nonstatic analytic vacuum exterior is to produce its Weyl representation on the entire domain and the weighted axial norm and twist defect on the compactified prolate rectangle. Their angular derivatives are continuous through the horizon endpoints, the norm has simple polar zeros and the infinity edge has the flat normalized values. The boundary estimates can then be deduced by an independent analytic argument.
-- source:
--   P. T. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Astérisque 321 (2008), Definition 1.1, Theorem 1.3, §2.2 and §§6–7, https://arxiv.org/abs/0806.0016. The classical theorem assumes I⁺-regularity. The proposed single-hypothesis revision of the mission statement is an open problem.

import Definitions.Def_NoHair_regularRodBoundaryData

open NoHair NoHair.Weyl Set
open scoped ContDiff Manifold

theorem NoHair.analytic_nonstatic_timelike_end_regular_rod_data {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] [IsManifold 𝓘(ℝ, E4) ω M]
    (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (htime : ∀ x ∈ E.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0)
    (hvac : ∀ x, F x = 0) (hanalytic : IsAnalyticBilinField g)
    (hnondeg : IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
      (domainOfOuterCommunications g T E.region))
    (hns : ¬ IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ ℓ J : ℝ, 0 ≤ ℓ ∧ (0 < ℓ ∨ J ≠ 0) ∧
      ∀ m a : ℝ, 0 < m → m^2-a^2 = ℓ^2 → m*a = J →
        ∃ (Ψ : E4 → M) (u : Weyl.ErnstPotentials),
          IsDiffeoOnto Ψ (kerrNewmanDOC m a 0) (domainOfOuterCommunications g T E.region) ∧
          u.IsSolution ∧ Weyl.IsWeylRepresentation m a (pullbackCoeffs g Ψ) u ∧
          Nonempty (Weyl.RegularRodBoundaryData u m ℓ J) := by
  sorry
