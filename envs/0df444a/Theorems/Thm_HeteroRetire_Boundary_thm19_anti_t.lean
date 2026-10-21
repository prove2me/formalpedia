-- Prove2me | Theorems.Thm_HeteroRetire_Boundary_thm19_anti_t
-- name    : HeteroRetire.Boundary.thm19_anti_t
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:20.253489+00:00
-- url     : https://prove2.me/theorems/abb1a226-b7bc-485b-8134-5d6774e4aa77
-- title:
--   Proof of Theorem 19, p. 40 (corrected) — dual stopping value decreases in time
-- statement:
--   Assume the growth condition on $[T-\ell,T]$ and that $\rho-r$ and $\|\vartheta\|^2$ are constant there. For $T-\ell\le s\le t\le T$ and $y>0$,
--   $$
--   \mathbb W(t,y)\le\mathbb W(s,y).
--   $$
--
--   This is the time comparison used to establish monotonicity of the free boundary.
--
--   **Formalization Note** The constant-coefficient condition corrects the source's time-shift argument on p. 39, which does not preserve a time-dependent generator.
-- source:
--   Jang, Xu, Zheng, Optimal Investment, Heterogeneous Consumption and Best Time for Retirement, arXiv:2008.00392v2, proof of Theorem 19, pp. 39–40

import Mathlib
import Definitions.Def_HeteroRetire_Boundary_Market
import Definitions.Def_HeteroRetire_Boundary_Model

namespace HeteroRetire.Boundary

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- Proof of Theorem 19, p. 40 (corrected): the stopping value
decreases in time on the aged interval. -/
theorem thm19_anti_t {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›)
    {n : ℕ} (M : Market n) (hM : M.Standing)
    (Z : ℝ → Ω → ℝ) (hZ : IsDualNoise P 𝔽 M Z)
    (ell : ℝ) (I' L' : ℝ → ℝ)
    (h18 : Assumption18 M ell I' L') (hconst : ConstOnAged M ell) :
    ∀ s ∈ Icc (M.T - ell) M.T, ∀ t ∈ Icc s M.T, ∀ y : ℝ,
      0 < y → Wdual P 𝔽 M Z t y ≤ Wdual P 𝔽 M Z s y := by sorry

end HeteroRetire.Boundary
