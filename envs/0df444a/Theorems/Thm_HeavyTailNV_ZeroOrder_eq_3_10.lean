-- Prove2me | Theorems.Thm_HeavyTailNV_ZeroOrder_eq_3_10
-- name    : HeavyTailNV.ZeroOrder.eq_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:18.281164+00:00
-- url     : https://prove2.me/theorems/18db57a2-9a9a-4772-ac47-a56899a75bb1
-- title:
--   (3.10), p. 14 — on 0 ≤ q ≤ q₀ the robust objective (1 − η)q + Π_{1,α}(q) equals m₁ − q(η − η₀)
-- statement:
--   Let $\alpha>1$, $m_\alpha>m_1^\alpha>0$, $\eta_0=1-(m_1^\alpha/m_\alpha)^{1/(\alpha-1)}$ and $q_0=\frac{\alpha-1}{\alpha}(m_\alpha/m_1)^{1/(\alpha-1)}$, and let $\Pi_{1,\alpha}(q)=\sup_{F\in\mathcal F_{1,\alpha}}\mathbb E_F[\tilde d-q]^+$. For every critical ratio $\eta\in[0,1)$ and every $q$ with $0\le q\le q_0$,
--   $$(1-\eta)q+\Pi_{1,\alpha}(q)=m_1-q\Big(\eta-1+\Big(\frac{m_1^\alpha}{m_\alpha}\Big)^{1/(\alpha-1)}\Big)=m_1-q(\eta-\eta_0).$$
--
--   On the interval $[0,q_0]$ the robust newsvendor objective is affine in $q$ with slope $\eta_0-\eta$, so its minimizer over that interval is $0$ when $\eta<\eta_0$, $q_0$ when $\eta>\eta_0$, and any point when $\eta=\eta_0$.
--
--   **Formalization Note** The paper writes (3.10) as an equality of minima over $[0,q_0]$; the item states the pointwise identity of the two objectives on $[0,q_0]$, from which the equality of minima follows. The range $\eta\in[0,1)$ is the paper's standing range of the critical ratio (p. 2).
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, p. 14, (3.10) in the proof of Proposition 3.2

import Mathlib
import Definitions.Def_HeavyTailNV_ZeroOrder_Model

namespace HeavyTailNV.ZeroOrder

/-- Display (3.10) (arXiv:1806.05379v2, p. 14): on `0 ≤ q ≤ q₀` the robust newsvendor objective
`(1 - η) q + Π_{1,α}(q)` equals `m₁ - q (η - η₀)`, for every critical ratio `η ∈ [0, 1)`. -/
theorem eq_3_10 (α m1 ma : ℝ) (hα : 1 < α) (hm1 : 0 < m1) (hma : m1 ^ α < ma) :
    ∀ η q : ℝ, 0 ≤ η → η < 1 → 0 ≤ q → q ≤ q0 m1 ma α →
      HeavyTailNV.Tail.robustCost m1 ma α η q = m1 - q * (η - eta0 m1 ma α) := by sorry

end HeavyTailNV.ZeroOrder
