-- Prove2me | Theorems.Thm_HeavyTailNV_ZeroOrder_proposition_3_2
-- name    : HeavyTailNV.ZeroOrder.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:26.644989+00:00
-- url     : https://prove2.me/theorems/5c6ed6fc-874b-44e8-83af-fa7ff0269308
-- title:
--   Proposition 3.2, p. 13 — η₀ ∈ (0,1); q* = 0 for η ∈ [0, η₀); every optimal q* ≥ q₀ > 0 for η ∈ (η₀, 1); [0, q₀] optimal at η = η₀
-- statement:
--   Let $\alpha>1$ and $m_\alpha>m_1^\alpha>0$, let $\mathcal F_{1,\alpha}$ be the set of laws on $[0,\infty)$ with mean $m_1$ and $\alpha$-th moment $m_\alpha$, and consider the distributionally robust newsvendor problem
--   $$\min_{q\ge 0}\ \Big((1-\eta)q+\sup_{F\in\mathcal F_{1,\alpha}}\mathbb E_F[\tilde d-q]^+\Big)\tag{3.2}$$
--   with critical ratio $\eta\in[0,1)$. Define the threshold critical ratio and the threshold order quantity
--   $$\eta_0=1-\Big(\frac{m_1^\alpha}{m_\alpha}\Big)^{1/(\alpha-1)},\qquad q_0=\frac{\alpha-1}{\alpha}\Big(\frac{m_\alpha}{m_1}\Big)^{1/(\alpha-1)}.$$
--   Then $\eta_0\in(0,1)$, and:
--
--   1. for every $\eta\in[0,\eta_0)$, the only optimal order quantity is $q^*=0$;
--   2. for every $\eta\in(\eta_0,1)$, an optimal order quantity exists, and every optimal order quantity $q^*$ satisfies $q^*>0$ and $q^*\ge q_0$;
--   3. for $\eta=\eta_0$, every $q\in[0,q_0]$ is an optimal order quantity.
--
--   For any moment order $\alpha>1$, however high, there is a range of small critical ratios in which the robust newsvendor orders nothing; this generalizes the zero-order region of Scarf's mean–variance model ($\alpha=2$).
--
--   **Formalization Note** "The optimal order quantity is given as $q^*=0$" in (a) is stated as: the set of minimizers of (3.2) over $q\ge0$ is exactly $\{0\}$. In (b) the existence of an optimal order quantity is stated explicitly, so that the lower bound is not vacuous; strict positivity is stated as a separate conjunct. Optimality is over $q\in[0,\infty)$ as in (3.2), not over $\mathbb R$.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, p. 13, Proposition 3.2 (proof p. 14)

import Mathlib
import Definitions.Def_HeavyTailNV_ZeroOrder_Model

namespace HeavyTailNV.ZeroOrder

/-- Proposition 3.2 (arXiv:1806.05379v2, p. 13). With `η₀ = 1 - (m₁^α/m_α)^{1/(α-1)} ∈ (0, 1)`:
(a) for `η ∈ [0, η₀)` the unique optimal order quantity of (3.2) is `q* = 0`;
(b) for `η ∈ (η₀, 1)` an optimal order quantity exists, and every optimal order quantity is
strictly positive and at least `q₀ = ((α - 1)/α)(m_α/m₁)^{1/(α-1)}`;
(c) for `η = η₀` every `q ∈ [0, q₀]` is an optimal order quantity. -/
theorem proposition_3_2 (α m1 ma : ℝ) (hα : 1 < α) (hm1 : 0 < m1) (hma : m1 ^ α < ma) :
    eta0 m1 ma α ∈ Set.Ioo 0 1 ∧
    (∀ η : ℝ, 0 ≤ η → η < eta0 m1 ma α →
      {q : ℝ | IsOptimalOrder m1 ma α η q} = {0}) ∧
    (∀ η : ℝ, eta0 m1 ma α < η → η < 1 →
      (∃ q : ℝ, IsOptimalOrder m1 ma α η q) ∧
      ∀ q : ℝ, IsOptimalOrder m1 ma α η q → 0 < q ∧ q0 m1 ma α ≤ q) ∧
    (∀ q ∈ Set.Icc 0 (q0 m1 ma α), IsOptimalOrder m1 ma α (eta0 m1 ma α) q) := by sorry

end HeavyTailNV.ZeroOrder
