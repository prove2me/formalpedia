-- Prove2me | Theorems.Thm_NoHair_analytic_nonstatic_timelike_end_rod_profile
-- name    : NoHair.analytic_nonstatic_timelike_end_rod_profile
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T10:00:10.383945+00:00
-- url     : https://prove2.me/theorems/6d79b83a-d028-4710-a090-a4cca5678f31
-- title:
--   Global Weyl chart and rod estimates for a nonstatic analytic vacuum exterior with a timelike reference end
-- statement:
--   For a nonstatic exterior in the revised analytic vacuum problem, construct a global comparison chart and an axial Ernst map from the geometric data of the spacetime. The horizon half-length $\ell$ and angular momentum $J$ determine the comparison parameters by $m^2-a^2=\ell^2$ and $ma=J$. In exterior Weyl coordinates the unknown metric is reconstructed from the map by the normalized quadratures. Its axial norm and twist have the finite normalized bounds and uniform asymptotics of the single-interval boundary profile. Establishing global rigidity, the orbit space, and control at the axis and interval endpoints from the stated hypotheses belongs to this geometric task.
-- source:
--   P. T. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Astérisque 321 (2008), Definition 1.1, Theorem 1.3, §2.2 and §§6–7, https://arxiv.org/abs/0806.0016. The classical theorem assumes I⁺-regularity. The proposed single-hypothesis revision of the mission statement is an open problem.

import Definitions.Def_NoHair_weylBoundaryProfile

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.analytic_nonstatic_timelike_end_rod_profile {M : Type*} [TopologicalSpace M]
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
          Weyl.HasProfileEstimates u (Weyl.rodBoundaryProfile m ℓ J) := by
  sorry
