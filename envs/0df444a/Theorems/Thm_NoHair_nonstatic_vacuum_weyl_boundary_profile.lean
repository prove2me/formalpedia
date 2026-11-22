-- Prove2me | Theorems.Thm_NoHair_nonstatic_vacuum_weyl_boundary_profile
-- name    : NoHair.nonstatic_vacuum_weyl_boundary_profile
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T22:47:30.700715+00:00
-- url     : https://prove2.me/theorems/7cb13903-08f8-4a64-9669-fd0b8f1fa2ed
-- title:
--   Weyl reduction and normalized axis and infinity estimates for the unknown vacuum exterior
-- statement:
--   Starting from the nonstatic axisymmetric stationary vacuum black-hole hypotheses, construct the global Weyl exterior, its angular momentum $J$, a single horizon interval of half-length $\ell$, and the normalized vacuum Ernst pair for the pulled-back metric. For the mass and spin matched to $\ell,J$, put $r=m+u$ and $c=z/u$, where $u$ is the mean of the focal distances. Derive from the geometry that $X/[(1-c^2)r^2]$ stays between positive constants and $(Y-2J(3c-c^3))/[(1-c^2)r^2]$ stays bounded, with these quantities tending uniformly to one and zero at infinity. On the interior of a positive-length horizon interval, the axial norm must have a limit. Control at the interval endpoints, including the puncture for a degenerate horizon, is part of the obligation. The statement quantifies over the original spacetime hypotheses.
-- source:
--   P. T. Chruściel and J. L. Costa, On uniqueness of stationary vacuum black holes, §§6.4–6.7, eqs. (6.13)–(6.18), (6.45)–(6.47) and Cor. 6.3, https://arxiv.org/abs/0806.0016. For the degenerate end see Amsel et al., pp. 3–5, eqs. (6)–(16), https://arxiv.org/abs/0906.2367. For the global regularity hypotheses see Chruściel, Costa and Heusler, Def. 2.1 and Thm. 3.2, https://arxiv.org/abs/1205.6112.

import Definitions.Def_NoHair_weylBoundaryProfile

open Filter Topology

open scoped ContDiff Manifold

namespace NoHair

theorem nonstatic_vacuum_weyl_boundary_profile {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g F : BilinField M) (T : VecField M)
    (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ) (h : IsStationaryBlackHole g F T φ E)
    (hvac : ∀ x, F x = 0) (ρ : ℝ → M → M) (hρ : IsAxialSymmetry g F φ ρ)
    (hns : ¬ IsStaticOn g φ (domainOfOuterCommunications g T E.region)) :
    ∃ ℓ J : ℝ, 0 ≤ ℓ ∧ (0 < ℓ ∨ J ≠ 0) ∧
      ∀ m a : ℝ, 0 < m → m^2-a^2 = ℓ^2 → m*a = J →
        ∃ (Ψ : E4 → M) (u : Weyl.ErnstPotentials),
          IsDiffeoOnto Ψ (kerrNewmanDOC m a 0) (domainOfOuterCommunications g T E.region) ∧
          u.IsSolution ∧ Weyl.HasProfileEstimates u (Weyl.rodBoundaryProfile m ℓ J) ∧
          (∀ z : ℝ, |z| < ℓ → ∃ L : ℝ,
            Tendsto (fun s : ℝ => u.normSq (s,z)) atBot (𝓝 L)) ∧
          Weyl.IsWeylRepresentation m a (pullbackCoeffs g Ψ) u := by
  sorry

end NoHair
