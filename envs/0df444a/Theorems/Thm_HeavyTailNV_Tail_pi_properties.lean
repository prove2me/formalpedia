-- Prove2me | Theorems.Thm_HeavyTailNV_Tail_pi_properties
-- name    : HeavyTailNV.Tail.pi_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:27:06.97852+00:00
-- url     : https://prove2.me/theorems/b28c96ce-37b2-4d6b-9e8f-4f2b53ac805a
-- title:
--   §2.1, p. 6 — the worst-case shortage Π_{1,α} is non-increasing, convex, equals m₁ − q for q ≤ 0, and vanishes at infinity
-- statement:
--   Let $\alpha>1$, $m_1>0$ and $m_\alpha>m_1^\alpha$, and let $\mathcal F_{1,\alpha}$ be the set of probability laws on $[0,\infty)$ with mean $m_1$ and $\alpha$th moment $m_\alpha$. For a real order quantity $q$, the worst-case expected shortage is
--
--   $$\Pi_{1,\alpha}(q)=\sup_{F\in\mathcal F_{1,\alpha}}\mathbb E_F[(\tilde d-q)^+].$$
--
--   Then:
--   1. $\Pi_{1,\alpha}$ is non-increasing on $\mathbb R$;
--   2. $\Pi_{1,\alpha}$ is convex on $\mathbb R$;
--   3. $\Pi_{1,\alpha}(q)+q=m_1$ for every $q\le 0$;
--   4. $\Pi_{1,\alpha}(q)\to 0$ as $q\to\infty$.
--
--   These four properties characterize $\Pi_{1,\alpha}$ as the stop-loss transform of a single non-negative demand law, which is how the representation (2.1) arises.
--
--   **Formalization Note** The paper states these properties for a general ambiguity set with finite mean; this item states them for the paper's set $\mathcal F_{1,\alpha}$, the instance used in §4. The supremum is the real supremum of a nonempty set bounded above by $m_1+|q|$. Mission 02 of this series states the same item in its own namespace.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, §2.1, p. 6, the properties of Π following (2.1), specialized to (3.1), p. 10

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model

namespace HeavyTailNV.Tail

open Filter Topology

theorem pi_properties (α m1 ma : ℝ) (hα : 1 < α) (hm1 : 0 < m1) (hma : m1 ^ α < ma) :
    Antitone (worstCase m1 ma α) ∧
    ConvexOn ℝ Set.univ (worstCase m1 ma α) ∧
    (∀ q : ℝ, q ≤ 0 → worstCase m1 ma α q + q = m1) ∧
    Tendsto (worstCase m1 ma α) atTop (𝓝 0) := by sorry

end HeavyTailNV.Tail
