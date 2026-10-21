-- Prove2me | Theorems.Thm_HeteroRetire_Boundary_theorem_19
-- name    : HeteroRetire.Boundary.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:21.459298+00:00
-- url     : https://prove2.me/theorems/fccce8d3-e74a-47ef-b7a6-5cc43506d134
-- title:
--   Theorem 19, p. 18 (corrected) — monotonic retirement boundary and terminal ratio
-- statement:
--   Assume the growth condition on $[T-\ell,T]$ and that the dual diffusion's drift $\rho-r$ and variance rate $\|\vartheta\|^2$ are constant throughout that interval. Then the retirement boundary is nondecreasing on the aged interval and has the left limit
--   $$
--   b(T-)=\lim_{t\uparrow T}b(t)=\frac{L(T)}{I(T)}.
--   $$
--
--   The result locates the near-retirement free boundary and identifies its terminal threshold.
--
--   **Formalization Note** The additional constant-coefficient condition repairs the paper's time-shift argument: with a time-dependent variance rate, the boundary can decrease despite Assumption 18. The boundary is extended real valued so $b(T)=+\infty$ remains distinct from its finite left limit.
-- source:
--   Jang, Xu, Zheng, Optimal Investment, Heterogeneous Consumption and Best Time for Retirement, arXiv:2008.00392v2, Theorem 19, p. 18; proof pp. 39–40

import Mathlib
import Definitions.Def_HeteroRetire_Boundary_Market
import Definitions.Def_HeteroRetire_Boundary_Model

namespace HeteroRetire.Boundary

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- Theorem 19, p. 18 (corrected): the aged free boundary is
nondecreasing and approaches the labor-cost-to-income ratio. -/
theorem theorem_19 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›)
    {n : ℕ} (M : Market n) (hM : M.Standing)
    (Z : ℝ → Ω → ℝ) (hZ : IsDualNoise P 𝔽 M Z)
    (ell : ℝ) (I' L' : ℝ → ℝ)
    (h18 : Assumption18 M ell I' L') (hconst : ConstOnAged M ell) :
    MonotoneOn (bdry P 𝔽 M Z) (Icc (M.T - ell) M.T) ∧
    Tendsto (bdry P 𝔽 M Z) (𝓝[<] M.T)
      (𝓝 ((M.L M.T / M.I M.T : ℝ) : EReal)) := by sorry

end HeteroRetire.Boundary
