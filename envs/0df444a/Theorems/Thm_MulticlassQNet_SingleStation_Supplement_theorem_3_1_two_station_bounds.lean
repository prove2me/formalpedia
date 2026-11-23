-- Prove2me | Theorems.Thm_MulticlassQNet_SingleStation_Supplement_theorem_3_1_two_station_bounds
-- name    : MulticlassQNet.SingleStation.Supplement.theorem_3_1_two_station_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:30:08.432513+00:00
-- url     : https://prove2.me/theorems/00d34462-29ef-42e1-8278-e840ed49a359
-- title:
--   Theorem 3.1 — the seven mean-response-time inequalities (2)–(8) of the two-station network
-- statement:
--   Consider the two-station network of §3: class 1 (type 1 at station 1) and class 2 (type 2 at station 1) arrive as Poisson streams of rates $\lambda_1,\lambda_2\ge0$ and are served at the common rate $\mu_1$; class 1 jobs then become class 3 and are served at station 2 at rate $\mu_2$. Assume $\lambda_1+\lambda_2<\mu_1$ and $\lambda_1<\mu_2$. Let $x_r$ be the mean response time of class $r$ and $n_r$ its steady-state mean number in system; class 1 and class 3 have throughput $\lambda_1$ and class 2 has throughput $\lambda_2$, so $n_1=\lambda_1x_1$, $n_2=\lambda_2x_2$, $n_3=\lambda_1x_3$.
--
--   For every Markovian scheduling policy (idling and preemption allowed) satisfying Assumption A,
--
--   $$\begin{aligned}
--   \lambda_1x_1+\lambda_2x_2&\ge\frac{\lambda_1+\lambda_2}{\mu_1-\lambda_1-\lambda_2},&(2)\qquad
--   x_1&\ge\frac1{\mu_1-\lambda_1},&(3)\\
--   x_2&\ge\frac1{\mu_1-\lambda_2},&(4)\qquad
--   x_3&\ge\frac1{\mu_2},&(5)\\
--   x_1+x_3&\ge\frac1{\mu_2-\lambda_1},&(6)\qquad
--   \lambda_2x_2+\lambda_1x_3&\ge\frac{\lambda_1+\lambda_2}{\mu_1+\mu_2-\lambda_2},&(7)\\
--   2\lambda_1x_1+\lambda_2x_2+\lambda_1x_3&\ge\frac{3\lambda_1+\lambda_2}{\mu_1+\mu_2-2\lambda_1-\lambda_2}.&(8)
--   \end{aligned}$$
--
--   Each inequality is stated for the mean numbers in system: (3) and (5) are multiplied by $\lambda_1$, (4) by $\lambda_2$, and (6) by $\lambda_1$.
--
--   These are the $2^3-1$ potential-function bounds of the example, one per nonempty class set. Minimizing $\sum_r c_rx_r$ subject to them gives a lower bound on the optimal cost of the network.
--
--   **Formalization Note** The network is `twoStation` (an instance of the published network record, classes indexed `0,1,2`); policies and Assumption A are the published `Policy` and `AssumptionA`. Following the convention of the series, $x_r$ enters only through $\lambda_rx_r=n_r$ (`meanNum π r`). When the class throughput is positive the multiplied inequality is equivalent to the printed one; when it is zero the class has no customers, its response time is undefined, and the multiplied inequality reads $n_r\ge0$. All denominators are positive under the stability assumptions.
--
--   Differences from the source:
--   - encoding: (3)–(6) bound the unweighted response times $x_1,x_2,x_3,x_1+x_3$ → Lean bounds $\lambda_1x_1=n_1$, $\lambda_2x_2=n_2$, $\lambda_1x_3=n_3$, $\lambda_1(x_1+x_3)=n_1+n_3$; reason: by Little's law $x_r=n_r/\lambda_r$ is defined only when the throughput is positive, and the multiplied form is equivalent there without dividing by zero or assuming every stream positive
--   - reading: the second-station rate is written $\mu_3$ on p. 8 and $\mu_2$ in the theorem → Lean has one parameter `mu2`; reason: both name the class-3 service rate at station 2
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), p. 9, Theorem 3.1, Eqs. (2)–(8); setting pp. 7–8, §3

import Mathlib
import Definitions.Def_MulticlassQNet_FirstOrder_Network
import Definitions.Def_MulticlassQNet_FirstOrder_Dynamics
import Definitions.Def_MulticlassQNet_SingleStation_Supplement_TwoStation

namespace MulticlassQNet.SingleStation.Supplement

open MulticlassQNet.FirstOrder

/-- Theorem 3.1 (p. 9): in the two-station network of §3, for every policy satisfying
Assumption A, the seven inequalities (2)–(8), each written with `λ_r x_r = n̄_r` (the mean
number of class-`r` customers): classes 1 and 3 have throughput `λ₁`, class 2 has `λ₂`, and an
inequality on an unweighted `x_r` is multiplied by that class's throughput. -/
theorem theorem_3_1_two_station_bounds (lam1 lam2 mu1 mu2 : ℝ) (h1 : 0 ≤ lam1) (h2 : 0 ≤ lam2)
    (hm1 : 0 < mu1) (hm2 : 0 < mu2) (hst1 : lam1 + lam2 < mu1) (hst2 : lam1 < mu2)
    (P : Policy (twoStation lam1 lam2 mu1 mu2 h1 h2 hm1 hm2)) (π : (Fin 3 → ℕ) → ℝ)
    (hA : P.AssumptionA π) :
    -- (2) λ₁x₁ + λ₂x₂ ≥ (λ₁ + λ₂)/(μ₁ − λ₁ − λ₂)
    (lam1 + lam2) / (mu1 - lam1 - lam2) ≤ meanNum π 0 + meanNum π 1 ∧
    -- (3) x₁ ≥ 1/(μ₁ − λ₁)
    lam1 / (mu1 - lam1) ≤ meanNum π 0 ∧
    -- (4) x₂ ≥ 1/(μ₁ − λ₂)
    lam2 / (mu1 - lam2) ≤ meanNum π 1 ∧
    -- (5) x₃ ≥ 1/μ₂
    lam1 / mu2 ≤ meanNum π 2 ∧
    -- (6) x₁ + x₃ ≥ 1/(μ₂ − λ₁)
    lam1 / (mu2 - lam1) ≤ meanNum π 0 + meanNum π 2 ∧
    -- (7) λ₂x₂ + λ₁x₃ ≥ (λ₁ + λ₂)/(μ₁ + μ₂ − λ₂)
    (lam1 + lam2) / (mu1 + mu2 - lam2) ≤ meanNum π 1 + meanNum π 2 ∧
    -- (8) 2λ₁x₁ + λ₂x₂ + λ₁x₃ ≥ (3λ₁ + λ₂)/(μ₁ + μ₂ − 2λ₁ − λ₂)
    (3 * lam1 + lam2) / (mu1 + mu2 - 2 * lam1 - lam2) ≤
      2 * meanNum π 0 + meanNum π 1 + meanNum π 2 := by sorry

end MulticlassQNet.SingleStation.Supplement
