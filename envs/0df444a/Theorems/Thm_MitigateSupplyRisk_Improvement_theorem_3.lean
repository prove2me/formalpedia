-- Prove2me | Theorems.Thm_MitigateSupplyRisk_Improvement_theorem_3
-- name    : MitigateSupplyRisk.Improvement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:47.207518+00:00
-- url     : https://prove2.me/theorems/7fe25a30-0678-438e-a760-91c11f8d5a66
-- title:
--   Theorem 3, p. 496 — with η = 0, Π₁(a) is concave in the reliability index, and an interior optimum satisfies (8) (with the factor r + p − v restored)
-- statement:
--   Consider early commitment to one supplier with no committed cost, $\eta = 0$, so that $\varphi = (r+p-c)/(r+p-v)$. Assume that the supplier's marginal reliability improvement is decreasing: for every $\xi$, the map $a \mapsto G(\xi, a)$ is concave on $[a^0, \infty)$. Then:
--
--   1. **Concavity.** The first-stage expected profit $\Pi_1(a) = -m z(a) + \theta \Pi_2^*(a) + (1-\theta)\Pi_2^*(a^0)$ of Eq. (7) is a concave function of the reliability index on $[a^0, \infty)$.
--
--   2. **First-order condition.** Let $a^* > a^0$ maximize $\Pi_1$ over $[a^0, \infty)$ and let $q^* \ge 0$ maximize $\Pi_2(\cdot\,; a^*)$ over $q \ge 0$. Suppose $z$ is differentiable at $a^*$ and, for every $\xi \in [K - q^*, K]$, $a \mapsto G(\xi, a)$ is differentiable at $a^*$ with derivative $\partial_a G(\xi, a^*)$. Then
--   $$m\, z'(a^*) = \theta\,(r+p-v) \int_{K - q^*}^{K} \big(\varphi - F(K-\xi)\big)\, \frac{\partial G(\xi, a^*)}{\partial a}\, d\xi .$$
--   For $\theta > 0$ this is the paper's Eq. (8),
--   $$\frac{m}{\theta}\, z'(a^*) = (r+p-v)\int_{K-q^*}^{K} \Big(\big(\varphi - F(K - \xi)\big) \frac{\partial G(\xi, a^*)}{\partial a}\Big)\, d\xi .$$
--
--   Concavity of $\Pi_1$ means the firm's improvement problem has no spurious local optima, and (8) balances the marginal cost of improvement against its marginal expected benefit, which accrues only through capacity losses in the window $[K-q^*, K]$ where the loss actually limits delivery.
--
--   **Formalization Note** (i) Eq. (8) as printed omits the factor $r+p-v$ on the right; it holds as printed only when $r+p-v = 1$, as in all of the paper's numerical examples. The Lean statement restores it. (ii) The paper's hypothesis $\partial^2 G/\partial a^2 \le 0$ is read as concavity of $G(\xi, \cdot)$ on $[a^0, \infty)$, which is equivalent for twice-differentiable $G$ and weaker otherwise. (iii) "The optimal index satisfies (8)" is the first-order condition at an interior optimum $a^* > a^0$; the differentiability of $z$ and of $G(\xi,\cdot)$ at $a^*$, which (8) presupposes, is assumed explicitly. (iv) The identity is stated multiplied by $\theta$, so it also covers $\theta = 0$; the derivative of $G$ is passed in as a function `dG` with a pointwise `HasDerivAt` hypothesis on $[K-q^*, K]$. (v) $q^*$ is an arbitrary optimal order at $a^*$.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 496 (PDF 8), Theorem 3, Eq. (8); p. 497 (PDF 9), remark after Theorem 3

import Mathlib
import Definitions.Def_MitigateSupplyRisk_Improvement_Model
import Definitions.Def_MitigateSupplyRisk_Improvement_FirstStage

open MeasureTheory ProbabilityTheory Set

namespace MitigateSupplyRisk.Improvement

theorem theorem_3 (M : Model) (I : Effort) (hM : M.Assumptions) (hI : I.Assumptions)
    (hη : M.η = 0) (hG : ∀ ξ : ℝ, ConcaveOn ℝ (Ici I.a0) (fun a => M.G ξ a)) :
    ConcaveOn ℝ (Ici I.a0) (Pi1 M I) ∧
    ∀ (aStar qStar z' : ℝ) (dG : ℝ → ℝ),
      I.a0 < aStar → IsMaxOn (Pi1 M I) (Ici I.a0) aStar →
      0 ≤ qStar → IsMaxOn (fun q => M.Pi2 q aStar) (Ici 0) qStar →
      HasDerivAt I.z z' aStar →
      (∀ ξ ∈ Icc (M.K - qStar) M.K, HasDerivAt (fun a => M.G ξ a) (dG ξ) aStar) →
      I.m * z' = I.θ * ((M.r + M.p - M.v) *
        ∫ ξ in (M.K - qStar)..M.K, (M.φ - M.F (M.K - ξ)) * dG ξ) := by sorry

end MitigateSupplyRisk.Improvement
