-- Prove2me | Theorems.Thm_FreemiumActions_Threshold_theorem_1
-- name    : FreemiumActions.Threshold.theorem_1
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T08:59:30.76512+00:00
-- url     : https://prove2.me/theorems/1ce8df3a-0dea-4f58-8845-82b2bd2c8103
-- title:
--   Theorem 1 — optimal revenue is nondecreasing in engagement
-- statement:
--   Let $N\ge0$ and $E=\{0,\ldots,N\}$. The publisher chooses a deterministic stationary policy $y:E\to\{0,1\}$. At each level the player probabilities satisfy $p_M+p_I+p_Q=q_M+q_Q=1$, with all probabilities and $\alpha$ in $[0,1]$. Removing the offer gives $q_M=p_M+\alpha p_I$ and $q_Q=p_Q+(1-\alpha)p_I$. Conditional on action $a\in\{M,I\}$ the player advances one level with constant probability $\tau_a\in[0,1]$ or stays, and stays at level $N$ if already there; quitting is absorbing. Assume $p_M,q_M,\alpha$ are nondecreasing, $p_Q,q_Q,p_I$ nonincreasing, both quitting probabilities strictly positive, $\tau_I<\tau_M$, and $0\le\mu_I<\mu_M$. The immediate revenues are $r(e,1)=p_M(e)\mu_M+p_I(e)\mu_I$ and $r(e,0)=q_M(e)\mu_M$, with zero revenue after quitting. Let $n_y(e,j)=\sum_{t\ge0}(S_y^t)_{e,j}$ and $W_y(e)=\sum_j n_y(e,j)r(j,y(j))$. These are Assumptions 1–4 with the standing probability and revenue conventions.
--
--   Let $W(e)=\max_y W_y(e)$ over every deterministic stationary policy. Then
--   $$\forall e,e'\in E,\qquad e\le e'\ \Longrightarrow\ W(e)\le W(e').$$
--   The comparison includes state zero and does not assume Assumptions 5–7. This is a property of the optimized total reward, not an assumption on the model.
--
--   Differences from the source:
--   - encoding: engagement levels 0 through N, quit state −1 and controls 0 or 1 → Fin (N+1), Option with none for quitting, and Bool controls; reason: order-preserving state labels and true = offer; N=0 is retained
--   - reading: increase, decrease and increasing in Assumption 3 → weak monotonicity, with quitting positivity and tauM > tauI still strict; reason: the appendix uses nondecreasing and nonincreasing comparisons
--   - encoding: earns revenue, with muI < muM in Assumption 4 → 0 ≤ muI < muM; reason: makes the model’s implicit nonnegative-revenue convention explicit without normalizing either revenue
--   - encoding: real expected infinite-horizon total reward and visit counts → nonnegative infinite sums in ENNReal; policy values are finite sums of visits times rewards; reason: positive quitting on the finite state set makes these values finite; no truncation, discount or conversion of an infinite value to zero is used
--   - encoding: maximum over all stationary policies → indexed supremum over the finite nonempty set of all Bool-valued stationary policies; reason: a finite nonempty set of values has an attained maximum
-- source:
--   Sheng, Ryan and Nagarajan, Incentivized actions in freemium games, supplied source.pdf dated October 8, 2016, §5, Theorem 1, p. 17 (PDF p. 17); A.4, pp. 32–33; catalog DOI 10.1287/msom.2020.0925.

import Definitions.Def_FreemiumActions_Threshold_Values

namespace FreemiumActions.Threshold

theorem theorem_1 {N : ℕ} (d : Data N) (h : Assumptions14 d) :
    Monotone (optimalValue d) := by sorry

end FreemiumActions.Threshold
