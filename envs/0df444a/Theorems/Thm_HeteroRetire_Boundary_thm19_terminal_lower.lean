-- Prove2me | Theorems.Thm_HeteroRetire_Boundary_thm19_terminal_lower
-- name    : HeteroRetire.Boundary.thm19_terminal_lower
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T03:44:17.451283+00:00
-- url     : https://prove2.me/theorems/d2806e72-d113-4cf7-8907-e58bbfb10cea
-- title:
--   Proof of Theorem 19, p. 40 — terminal value, lower half: $b(T-)\ge L(T)/I(T)$
-- statement:
--   Assume the setting of Theorem 19: the growth condition (Assumption 18) holds on the aged interval $[T-\ell,T]$, and the dual diffusion's drift $\rho-r$ and variance rate $\|\vartheta\|^2$ are constant there. Let $b(t)=\inf\{y>0:\mathbb W(t,y)>0\}$ be the retirement boundary (with $\inf\emptyset=+\infty$). Then the boundary is asymptotically at least the labor-cost-to-income ratio at the mandatory retirement age:
--   $$
--   \liminf_{t\uparrow T} b(t)\ \ge\ \frac{L(T)}{I(T)},
--   $$
--   that is, for every real $c<L(T)/I(T)$ there is $\delta>0$ with $c\le b(t)$ for all $t\in(T-\delta,T)$.
--
--   This is the lower half of the terminal value $b(T-)=L(T)/I(T)$ in Theorem 19; the upper half follows from Proposition 17, $b(t)\le L(t)/I(t)$, and the continuity of $L$ and $I$.
--
--   **Formalization Note** The boundary is valued in the extended reals, and the left limit is expressed with the filter $\mathcal N_{<}(T)$ of left neighbourhoods of $T$. The hypotheses are exactly those of the corrected Theorem 19 in this mission.
-- source:
--   Jang, Xu, Zheng, Optimal Investment, Heterogeneous Consumption and Best Time for Retirement, arXiv:2008.00392v2, Theorem 19, p. 18; proof p. 40 (the argument excluding b(T-) < L(T)/I(T), Figure 6)

import Mathlib
import Definitions.Def_HeteroRetire_Boundary_Market
import Definitions.Def_HeteroRetire_Boundary_Model

namespace HeteroRetire.Boundary

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- Proof of Theorem 19, p. 40 (terminal value, lower half): the retirement
boundary cannot stay below the labor-cost-to-income ratio near `T`, i.e.
`b(T-) ≥ L(T)/I(T)`, stated as: every level below the ratio is eventually
a lower bound of `b` as `t ↑ T`. -/
theorem thm19_terminal_lower {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›)
    {n : ℕ} (M : Market n) (hM : M.Standing)
    (Z : ℝ → Ω → ℝ) (hZ : IsDualNoise P 𝔽 M Z)
    (ell : ℝ) (I' L' : ℝ → ℝ)
    (h18 : Assumption18 M ell I' L') (hconst : ConstOnAged M ell) :
    ∀ c : ℝ, c < M.L M.T / M.I M.T →
      ∀ᶠ t in 𝓝[<] M.T, (c : EReal) ≤ bdry P 𝔽 M Z t := by sorry

end HeteroRetire.Boundary
