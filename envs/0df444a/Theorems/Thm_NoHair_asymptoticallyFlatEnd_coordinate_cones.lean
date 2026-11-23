-- Prove2me | Theorems.Thm_NoHair_asymptoticallyFlatEnd_coordinate_cones
-- name    : NoHair.asymptoticallyFlatEnd_coordinate_cones
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:00:09.170798+00:00
-- url     : https://prove2.me/theorems/ae99afcb-e51f-487e-8029-c47c6d65e37b
-- title:
--   A quantitative timelike cone and time coordinate on a distant asymptotically flat end
-- statement:
--   At a point of an asymptotic end with Cartesian spatial radius $\rho\ge16|C|$, let $B=\psi^*g$ in the end coordinates. The spatial hyperplane $v^0=0$ is nonnegative for $B$. Every vector $u\partial_t+d\partial_1$ with $u>0$ and $2|d|\le u$ is timelike. For any two timelike vectors $v,w$ one has $B(v,w)v^0w^0<0$. Thus the sign of coordinate time distinguishes the two timelike cones. The result applies to any Lorentzian metric with the stated end-chart decay.
-- source:
--   P. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Section 2.2, pp. 6–7, equations (2.4)–(2.10) and the discussion of overlapping ends, https://arxiv.org/abs/0806.0016 . The numerical bound below is a sufficient estimate for the metric-component decay in the Prove2Me end chart.

import Definitions.Def_NoHair_spacetime

open NoHair Set
open scoped ContDiff Manifold BigOperators

theorem NoHair.asymptoticallyFlatEnd_coordinate_cones {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ, E4) ∞ M] {g F : BilinField M} {φ : ℝ → M → M}
    (E : AsymptoticallyFlatEnd g F φ)
    (hg : IsLorentzian g) (y : E4) (hy : y ∈ exteriorRegion E.R)
    (hfar : 16 * |E.C| ≤ spatialRadius y) :
    let L := mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) E.ψ y
    let B := fun v w : E4 => g (E.ψ y) (L v) (L w)
    (∀ v : E4, v 0 = 0 → 0 ≤ B v v) ∧
    (∀ u d : ℝ, 0 < u → 2 * |d| ≤ u →
      B (u • coordBasis 0 + d • coordBasis 1) (u • coordBasis 0 + d • coordBasis 1) < 0) ∧
    ∀ v w : E4, B v v < 0 → B w w < 0 → B v w * v 0 * w 0 < 0 := by
  sorry
