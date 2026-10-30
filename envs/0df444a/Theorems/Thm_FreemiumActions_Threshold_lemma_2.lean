-- Prove2me | Theorems.Thm_FreemiumActions_Threshold_lemma_2
-- name    : FreemiumActions.Threshold.lemma_2
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T08:59:41.805482+00:00
-- url     : https://prove2.me/theorems/5fbe8980-932b-4920-9829-5cee12b3c94e
-- title:
--   Lemma 2 — lower bounds for both constrained optimal values
-- statement:
--   Let $N\ge0$ and $E=\{0,\ldots,N\}$. The publisher chooses a deterministic stationary policy $y:E\to\{0,1\}$. At each level the player probabilities satisfy $p_M+p_I+p_Q=q_M+q_Q=1$, with all probabilities and $\alpha$ in $[0,1]$. Removing the offer gives $q_M=p_M+\alpha p_I$ and $q_Q=p_Q+(1-\alpha)p_I$. Conditional on action $a\in\{M,I\}$ the player advances one level with constant probability $\tau_a\in[0,1]$ or stays, and stays at level $N$ if already there; quitting is absorbing. Assume $p_M,q_M,\alpha$ are nondecreasing, $p_Q,q_Q,p_I$ nonincreasing, both quitting probabilities strictly positive, $\tau_I<\tau_M$, and $0\le\mu_I<\mu_M$. The immediate revenues are $r(e,1)=p_M(e)\mu_M+p_I(e)\mu_I$ and $r(e,0)=q_M(e)\mu_M$, with zero revenue after quitting. Let $n_y(e,j)=\sum_{t\ge0}(S_y^t)_{e,j}$ and $W_y(e)=\sum_j n_y(e,j)r(j,y(j))$. These are Assumptions 1–4 with the standing probability and revenue conventions.
--
--   For every engagement level $1\le e\le N$, the optimal values constrained to action $0$ or $1$ at every visit to $e$ satisfy both inequalities
--   $$W(e,y=0)\ge\frac{q_M(e)\mu_M}{1-q_M(e)},\qquad W(e,y=1)\ge\frac{p_M(e)\mu_M+p_I(e)\mu_I}{1-p_M(e)-p_I(e)}.$$
--   Both denominators are strictly positive quitting probabilities. Choices away from $e$ remain optimized over all stationary policies.
--
--   Differences from the source:
--   - encoding: engagement levels 0 through N, quit state −1 and controls 0 or 1 → Fin (N+1), Option with none for quitting, and Bool controls; reason: order-preserving state labels and true = offer; N=0 is retained
--   - reading: increase, decrease and increasing in Assumption 3 → weak monotonicity, with quitting positivity and tauM > tauI still strict; reason: the appendix uses nondecreasing and nonincreasing comparisons
--   - encoding: earns revenue, with muI < muM in Assumption 4 → 0 ≤ muI < muM; reason: makes the model’s implicit nonnegative-revenue convention explicit without normalizing either revenue
--   - encoding: real expected infinite-horizon total reward and visit counts → nonnegative infinite sums in ENNReal; policy values are finite sums of visits times rewards; reason: positive quitting on the finite state set makes these values finite; no truncation, discount or conversion of an infinite value to zero is used
--   - encoding: maximum over all stationary policies → indexed supremum over the finite nonempty set of all Bool-valued stationary policies; reason: a finite nonempty set of values has an attained maximum
--   - reading: prose defines constrained stationary values while the second line of (27) uses the unconstrained continuation value in a self-loop → constrain the stationary action on every visit to e; reason: matches the prose on p. 17 and the resolved self-loop formulas in the proof on p. 32; it is not a one-step deviation
-- source:
--   Sheng, Ryan and Nagarajan, Incentivized actions in freemium games, supplied source.pdf dated October 8, 2016, A.4, Lemma 2, p. 32 (PDF p. 32), under Theorem 1’s Assumptions 1–4; catalog DOI 10.1287/msom.2020.0925.

import Definitions.Def_FreemiumActions_Threshold_Values

namespace FreemiumActions.Threshold

theorem lemma_2 {N : ℕ} (d : Data N) (h : Assumptions14 d)
    (e : Level N) (he : 1 ≤ e.val) :
    ENNReal.ofReal (d.qM e * d.muM / (1 - d.qM e)) ≤ constrainedValue d e false ∧
    ENNReal.ofReal ((d.pM e * d.muM + d.pI e * d.muI) /
      (1 - d.pM e - d.pI e)) ≤ constrainedValue d e true := by sorry

end FreemiumActions.Threshold
