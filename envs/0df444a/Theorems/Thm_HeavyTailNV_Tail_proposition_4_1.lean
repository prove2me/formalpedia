-- Prove2me | Theorems.Thm_HeavyTailNV_Tail_proposition_4_1
-- name    : HeavyTailNV.Tail.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:23:22.535712+00:00
-- url     : https://prove2.me/theorems/58fa31f9-bf75-4efa-95ea-470c3f5fdfbe
-- title:
--   Proposition 4.1, p. 30 — robust optimal orders are optimal for F*, and q*_η ∼ ((α−1)/α)(1/(1−η)) C*_η as η → 1
-- statement:
--   Let $\alpha>1$, $m_1>0$ and $m_\alpha>m_1^\alpha$, and let $\Pi_{1,\alpha}(q)=\sup_{F\in\mathcal F_{1,\alpha}}\mathbb E_F[(\tilde d-q)^+]$ be the worst-case expected shortage over non-negative demand laws with mean $m_1$ and $\alpha$th moment $m_\alpha$. For a critical ratio $\eta\in(0,1)$ the distributionally robust newsvendor minimizes $(1-\eta)q+\Pi_{1,\alpha}(q)$ over $q\ge 0$. Let $q^*_\eta$ be any optimal order quantity for each $\eta\in(0,1)$, and let $C^*_\eta=(1-\eta)q^*_\eta+\Pi_{1,\alpha}(q^*_\eta)$ be the optimal cost. Then:
--   1. for every non-negative demand law $F^*$ whose expected shortage equals $\Pi_{1,\alpha}(q)$ at every $q\ge0$ (the law of Theorem 4.3(b)), $q^*_\eta$ is an optimal order quantity of the standard newsvendor $\min_{q\ge0}\,(1-\eta)q+\mathbb E_{F^*}[(\tilde d^*-q)^+]$;
--   2. as the critical ratio tends to one,
--
--   $$q^*_\eta\sim\frac{\alpha-1}{\alpha}\,\frac{1}{1-\eta}\,C^*_\eta,\qquad \eta\to1,$$
--
--   that is, the ratio of the two sides tends to $1$ as $\eta\uparrow1$.
--
--   The result gives the high-service-level behaviour of the robust order quantity directly in terms of the robust optimal cost and the tail index $\alpha$.
--
--   **Formalization Note** The statement quantifies over every selection $\eta\mapsto q^*_\eta$ of optimizers, as the page's "let $q^*_\eta$ be an optimal order quantity". The optimal cost $C^*_\eta$ is written as the cost at $q^*_\eta$, which is the minimum value. A non-negative law is determined by its expected shortages on $[0,\infty)$, so quantifying over every representing law is the same as speaking of the $F^*$ of Theorem 4.3(b). The limit $\eta\to1$ is taken from the left. The relation $\sim$ is stated as the ratio tending to $1$.
-- source:
--   Das, Dhara and Natarajan, On the heavy-tail behavior of the distributionally robust newsvendor, arXiv:1806.05379v2, p. 30, Proposition 4.1, (4.9); proof pp. 30–31

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model

namespace HeavyTailNV.Tail

open MeasureTheory Filter Topology

theorem proposition_4_1 (α m1 ma : ℝ) (hα : 1 < α) (hm1 : 0 < m1) (hma : m1 ^ α < ma)
    (qstar : ℝ → ℝ)
    (hopt : ∀ η ∈ Set.Ioo (0 : ℝ) 1,
      0 ≤ qstar η ∧ IsMinOn (robustCost m1 ma α η) (Set.Ici 0) (qstar η)) :
    (∀ Fstar : Measure ℝ, IsProbabilityMeasure Fstar → Fstar (Set.Iio 0) = 0 →
      (∀ q : ℝ, 0 ≤ q → Integrable (fun w : ℝ => max (w - q) 0) Fstar ∧
        (∫ w, max (w - q) 0 ∂Fstar) = worstCase m1 ma α q) →
      ∀ η ∈ Set.Ioo (0 : ℝ) 1,
        IsMinOn (fun q : ℝ => (1 - η) * q + ∫ w, max (w - q) 0 ∂Fstar) (Set.Ici 0)
          (qstar η)) ∧
    Tendsto
      (fun η : ℝ => qstar η /
        ((α - 1) / α * (1 / (1 - η)) * robustCost m1 ma α η (qstar η)))
      (𝓝[<] 1) (𝓝 1) := by sorry

end HeavyTailNV.Tail
