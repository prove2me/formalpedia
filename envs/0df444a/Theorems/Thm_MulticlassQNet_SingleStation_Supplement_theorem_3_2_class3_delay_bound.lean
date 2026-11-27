-- Prove2me | Theorems.Thm_MulticlassQNet_SingleStation_Supplement_theorem_3_2_class3_delay_bound
-- name    : MulticlassQNet.SingleStation.Supplement.theorem_3_2_class3_delay_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T05:30:37.017933+00:00
-- url     : https://prove2.me/theorems/0af31147-88da-407f-b52c-ff2180655b88
-- title:
--   Theorem 3.2 — under 2λ₁ > max(μ₁, μ₂) the class-3 response time exceeds 1/μ₂ by an explicit amount (13)
-- statement:
--   In the two-station network of §3 (arrival rates $\lambda_1,\lambda_2\ge0$, common first-station rate $\mu_1$, second-station rate $\mu_2$, with $\lambda_1+\lambda_2<\mu_1$ and $\lambda_1<\mu_2$), suppose moreover that
--
--   $$2\lambda_1>\max(\mu_1,\mu_2).$$
--
--   Then for every Markovian scheduling policy satisfying Assumption A, the mean response time $x_3$ of class 3 (type 1 customers at station 2) satisfies
--
--   $$x_3\ \ge\ \frac{2\lambda_1-\max(\mu_1,\mu_2)}{\mu_1+\mu_2-\max(\mu_1,\mu_2)}\cdot\frac{\mu_1}{\mu_2(\mu_1+\mu_2)}+\frac1{\mu_2}.\qquad(13)$$
--
--   Theorem 3.1 alone allows $x_3$ to be as small as the mean service time $1/\mu_2$. Under heavy type-1 traffic this is not achievable by a stable policy, and (13) quantifies the excess waiting.
--
--   **Formalization Note** The bound is stated for $n_3=\lambda_1x_3$ (`meanNum π 2`), i.e. (13) multiplied by $\lambda_1$; the hypothesis gives $\lambda_1>0$, so this is equivalent to (13). No condition on $\lambda_2$ is added; $\lambda_2=0$ is allowed but not required.
--
--   Differences from the source:
--   - encoding: (13) bounds $x_3$ → Lean bounds $n_3=\lambda_1x_3$ by $\lambda_1$ times the right-hand side of (13); reason: Little's law, equivalent since $\lambda_1>\max(\mu_1,\mu_2)/2>0$
--   - reading: the second-station rate is written $\mu_3$ on pp. 8 and 12 and $\mu_2$ in (13) → Lean has one parameter `mu2`; reason: both name the class-3 service rate at station 2
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), p. 12, §3.1.1, Theorem 3.2, Eq. (13) (proof deferred to [Pasc])

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_SingleStation_Supplement_TwoStation

namespace MulticlassQNet.SingleStation.Supplement

open MulticlassQNet.FirstOrder

/-- Theorem 3.2 (p. 12): in the two-station network of §3 with `2λ₁ > max(μ₁, μ₂)`, every
policy satisfying Assumption A has
`x₃ ≥ [(2λ₁ − max(μ₁,μ₂))/(μ₁ + μ₂ − max(μ₁,μ₂))]·[μ₁/(μ₂(μ₁ + μ₂))] + 1/μ₂`, (13)
stated for `n̄₃ = λ₁ x₃` (class 3 has throughput `λ₁ > 0`). -/
theorem theorem_3_2_class3_delay_bound (lam1 lam2 mu1 mu2 : ℝ) (h1 : 0 ≤ lam1) (h2 : 0 ≤ lam2)
    (hm1 : 0 < mu1) (hm2 : 0 < mu2) (hst1 : lam1 + lam2 < mu1) (hst2 : lam1 < mu2)
    (hheavy : max mu1 mu2 < 2 * lam1)
    (P : Policy (twoStation lam1 lam2 mu1 mu2 h1 h2 hm1 hm2)) (π : (Fin 3 → ℕ) → ℝ)
    (hA : P.AssumptionA π) :
    lam1 * ((2 * lam1 - max mu1 mu2) / (mu1 + mu2 - max mu1 mu2) * (mu1 / (mu2 * (mu1 + mu2)))
      + 1 / mu2) ≤ meanNum π 2 := by sorry

end MulticlassQNet.SingleStation.Supplement
