-- Prove2me | Theorems.Thm_HeavyTailNV_ZeroOrder_proposition_3_1
-- name    : HeavyTailNV.ZeroOrder.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:23.812252+00:00
-- url     : https://prove2.me/theorems/a73782bc-72f9-443b-91b9-c7331ea7d4e9
-- title:
--   Proposition 3.1, p. 12 — Π_{1,α}(q) = m₁ − q(m₁^α/m_α)^{1/(α−1)} for 0 ≤ q ≤ q₀, attained by the two-point law (3.6)
-- statement:
--   Let $\alpha>1$ and $m_\alpha>m_1^\alpha>0$, and let $\mathcal F_{1,\alpha}$ be the set of laws on $[0,\infty)$ with mean $m_1$ and $\alpha$-th moment $m_\alpha$. Write $q_0=\frac{\alpha-1}{\alpha}(m_\alpha/m_1)^{1/(\alpha-1)}$ and let $F^*$ be the two-point law
--   $$\tilde d^*=\begin{cases}0 & \text{w.p. } 1-(m_1^\alpha/m_\alpha)^{1/(\alpha-1)},\\ (m_\alpha/m_1)^{1/(\alpha-1)} & \text{w.p. } (m_1^\alpha/m_\alpha)^{1/(\alpha-1)}.\end{cases}$$
--   Then $F^*\in\mathcal F_{1,\alpha}$, and for every $q$ with $0\le q\le q_0$,
--   $$\sup_{F\in\mathcal F_{1,\alpha}}\mathbb E_F[\tilde d-q]^+ = m_1-q\Big(\frac{m_1^\alpha}{m_\alpha}\Big)^{1/(\alpha-1)} = \mathbb E_{F^*}[\tilde d^*-q]^+ .$$
--
--   For small order quantities the worst-case expected shortage is linear in $q$, and the same two-point law is worst-case for every such $q$. This closed form drives the zero-order threshold of Proposition 3.2.
--
--   **Formalization Note** "The worst-case demand distribution is given as (3.6)" is stated as two facts: the law lies in $\mathcal F_{1,\alpha}$, and its expected shortage equals the supremum for every $q\in[0,q_0]$.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, p. 12, Proposition 3.1, (3.5)–(3.6)

import Mathlib
import Definitions.Def_HeavyTailNV_ZeroOrder_Model

namespace HeavyTailNV.ZeroOrder

open MeasureTheory

/-- Proposition 3.1 (arXiv:1806.05379v2, p. 12): for `0 ≤ q ≤ q₀` the worst-case expected
shortage over `F_{1,α}` is `m₁ - q (m₁^α/m_α)^{1/(α-1)}` (3.5), and the two-point law (3.6) lies in
`F_{1,α}` and attains it. -/
theorem proposition_3_1 (α m1 ma : ℝ) (hα : 1 < α) (hm1 : 0 < m1) (hma : m1 ^ α < ma) :
    twoPointLaw m1 ma α ∈ HeavyTailNV.Tail.ambiguitySet m1 ma α ∧
    ∀ q : ℝ, 0 ≤ q → q ≤ q0 m1 ma α →
      HeavyTailNV.Tail.worstCase m1 ma α q = m1 - q * (m1 ^ α / ma) ^ (1 / (α - 1)) ∧
      ∫ w, max (w - q) 0 ∂(twoPointLaw m1 ma α) = HeavyTailNV.Tail.worstCase m1 ma α q := by sorry

end HeavyTailNV.ZeroOrder
