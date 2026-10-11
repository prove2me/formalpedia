-- Prove2me | Theorems.Thm_KPZBallistic_penrose_thm_2_1
-- name    : KPZBallistic.penrose_thm_2_1
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T09:30:15.580971+00:00
-- url     : https://prove2.me/theorems/a257cf69-216b-40ab-9dcb-59db7d2a72bf
-- title:
--   Penrose Thm. 2.1: $E\xi_t(0)/t\to\rho_1$ and $L^p$ law of large numbers
-- statement:
--   In one-dimensional nearest-neighbour ballistic deposition on $\mathbb Z$ from a flat surface, let $h(t)=E[\xi_t(0)]$. There is a constant $\rho_1\in(0,\infty)$ such that
--
--   $$
--   \frac{h(t)}{t}\to\rho_1\qquad(t\to\infty),
--   $$
--
--   and moreover, for every $p\in[1,\infty)$, $\xi_t(0)/t\to\rho_1$ in $L^p(P)$ as $t\to\infty$.
--
--   The constant $\rho_1$ is the asymptotic growth speed of the interface; it is the centring for any fluctuation result.
-- source:
--   M. D. Penrose, Growth and roughness of the interface for ballistic deposition, J. Stat. Phys. 131 (2008), https://arxiv.org/abs/math/0608540, Section 2, Theorem 2.1 and eq. (2.11), p. 5 (case d = 1, nearest-neighbour model)

import Mathlib
import Definitions.Def_KPZBallistic_Defs

open MeasureTheory ProbabilityTheory Filter Topology

namespace KPZBallistic

theorem penrose_thm_2_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (τ : ℤ → ℕ → Ω → ℝ) (hτ : IsPoissonClocks P τ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun t : ℝ => (∫ ω, bdHeightReal τ t 0 ω ∂P) / t) atTop (𝓝 ρ) ∧
      ∀ p : ℝ, 1 ≤ p →
        Tendsto (fun t : ℝ => eLpNorm (fun ω => bdHeightReal τ t 0 ω / t - ρ)
          (ENNReal.ofReal p) P) atTop (𝓝 0) := by sorry

end KPZBallistic
