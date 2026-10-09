-- Prove2me | Theorems.Thm_HeavyTailNV_ZeroOrder_pi_properties
-- name    : HeavyTailNV.ZeroOrder.pi_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:26.585978+00:00
-- url     : https://prove2.me/theorems/e9de7775-78c4-415a-b1d4-28b00783648c
-- title:
--   §2.1, p. 6 — Π_{1,α} is non-increasing and convex, Π_{1,α}(q) + q = m₁ for q ≤ 0, and Π_{1,α}(q) → 0 as q → ∞
-- statement:
--   Let $\alpha>1$ and $m_\alpha>m_1^\alpha>0$, let $\mathcal F_{1,\alpha}$ be the set of laws on $[0,\infty)$ with mean $m_1$ and $\alpha$-th moment $m_\alpha$, and let $\Pi_{1,\alpha}(q)=\sup_{F\in\mathcal F_{1,\alpha}}\mathbb E_F[\tilde d-q]^+$ for $q\in\mathbb R$. Then:
--
--   1. $\Pi_{1,\alpha}$ is non-increasing on $\mathbb R$;
--   2. $\Pi_{1,\alpha}$ is convex on $\mathbb R$;
--   3. for every $q\le 0$, $\Pi_{1,\alpha}(q)+q=m_1$;
--   4. $$\lim_{q\to\infty}\Pi_{1,\alpha}(q)=0 .$$
--
--   These are the general properties of a worst-case stop-loss function noted in §2.1 of the paper for any ambiguity set with a specified mean, here for $\mathcal F_{1,\alpha}$. Convexity is what lets the proof of Proposition 3.2 pass from the interval $[0,q_0]$ to all of $[0,\infty)$.
--
--   **Formalization Note** The paper states these properties for a general ambiguity set $\mathcal F$ with finite mean; this item states them for $\mathcal F_{1,\alpha}$ only, where $\sup_{F}\mathbb E_F[\tilde d]=m_1$.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, §2.1, p. 6, the properties of Π following (2.1)

import Mathlib
import Definitions.Def_HeavyTailNV_ZeroOrder_Model

namespace HeavyTailNV.ZeroOrder

open Filter Topology

/-- The properties of `Π` (arXiv:1806.05379v2, §2.1, p. 6), for the ambiguity set `F_{1,α}`:
`Π_{1,α}` is non-increasing and convex, `Π_{1,α}(q) + q = m₁` for every `q ≤ 0`, and
`Π_{1,α}(q) → 0` as `q → ∞`. -/
theorem pi_properties (α m1 ma : ℝ) (hα : 1 < α) (hm1 : 0 < m1) (hma : m1 ^ α < ma) :
    Antitone (HeavyTailNV.Tail.worstCase m1 ma α) ∧
    ConvexOn ℝ Set.univ (HeavyTailNV.Tail.worstCase m1 ma α) ∧
    (∀ q : ℝ, q ≤ 0 → HeavyTailNV.Tail.worstCase m1 ma α q + q = m1) ∧
    Tendsto (HeavyTailNV.Tail.worstCase m1 ma α) atTop (𝓝 0) := by sorry

end HeavyTailNV.ZeroOrder
