-- Prove2me | Theorems.Thm_FreemiumActions_Threshold_theorem_2
-- name    : FreemiumActions.Threshold.theorem_2
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T09:00:52.34633+00:00
-- url     : https://prove2.me/theorems/760cada7-911e-4f47-a924-eb62e4ca894a
-- title:
--   Theorem 2 — existence of an optimal forward threshold policy
-- statement:
--   Let $N\ge0$ and $E=\{0,\ldots,N\}$. The publisher chooses a deterministic stationary policy $y:E\to\{0,1\}$. At each level the player probabilities satisfy $p_M+p_I+p_Q=q_M+q_Q=1$, with all probabilities and $\alpha$ in $[0,1]$. Removing the offer gives $q_M=p_M+\alpha p_I$ and $q_Q=p_Q+(1-\alpha)p_I$. Conditional on action $a\in\{M,I\}$ the player advances one level with constant probability $\tau_a\in[0,1]$ or stays, and stays at level $N$ if already there; quitting is absorbing. Assume $p_M,q_M,\alpha$ are nondecreasing, $p_Q,q_Q,p_I$ nonincreasing, both quitting probabilities strictly positive, $\tau_I<\tau_M$, and $0\le\mu_I<\mu_M$. The immediate revenues are $r(e,1)=p_M(e)\mu_M+p_I(e)\mu_I$ and $r(e,0)=q_M(e)\mu_M$, with zero revenue after quitting. Let $n_y(e,j)=\sum_{t\ge0}(S_y^t)_{e,j}$ and $W_y(e)=\sum_j n_y(e,j)r(j,y(j))$. These are Assumptions 1–4 with the standing probability and revenue conventions.
--
--   Assume further $\alpha(N)=1$, the adjacent-pair inequalities $\alpha(e+1)-\alpha(e)>q_M(e+1)-q_M(e)$ for $0\le e<N$, and precisely the printed Assumption 7:
--   $$1-\alpha(e+1)\le(1-\alpha(e))\frac{p_M(e+1)\tau_M+p_I(e+1)\tau_I}{p_Q(e+1)+p_M(e+1)\tau_M+p_I(e+1)\tau_I}\quad(1\le e<N).$$
--   The source asserts that there exist one stationary policy $y^*$ and a cutoff $e^*\in\{-1,\ldots,N\}$ such that
--   $$\forall y:E\to\{0,1\},\ \forall e\in E,\quad W_y(e)\le W_{y^*}(e),$$
--   $$y^*(e)=1\ (e\le e^*),\qquad y^*(e)=0\ (e>e^*).$$
--   The same policy works for every starting level, against every stationary competitor. No uniqueness or tie-breaking is asserted. The printed Assumption 7 excludes $e=0$; the resulting counterexample is retained in the source findings rather than repaired in this target.
--
--   Differences from the source:
--   - encoding: engagement levels 0 through N, quit state −1 and controls 0 or 1 → Fin (N+1), Option with none for quitting, and Bool controls; reason: order-preserving state labels and true = offer; N=0 is retained
--   - reading: increase, decrease and increasing in Assumption 3 → weak monotonicity, with quitting positivity and tauM > tauI still strict; reason: the appendix uses nondecreasing and nonincreasing comparisons
--   - encoding: earns revenue, with muI < muM in Assumption 4 → 0 ≤ muI < muM; reason: makes the model’s implicit nonnegative-revenue convention explicit without normalizing either revenue
--   - encoding: real expected infinite-horizon total reward and visit counts → nonnegative infinite sums in ENNReal; policy values are finite sums of visits times rewards; reason: positive quitting on the finite state set makes these values finite; no truncation, discount or conversion of an infinite value to zero is used
--   - reading: Assumption 6 says all e in E although e+1 is undefined at N → all adjacent pairs e,f in E with f=e+1; reason: states precisely the domain where the printed expression is defined
--   - encoding: threshold cutoff e* from −1 through N → initial-segment length k in Fin (N+2), offering exactly when e<k; reason: k=e*+1 preserves both boundary policies and both sides of the cutoff
-- source:
--   Sheng, Ryan and Nagarajan, Incentivized actions in freemium games, supplied source.pdf dated October 8, 2016, §5, Theorem 2, p. 21 (PDF p. 21); Assumptions 5–7, pp. 19–20; A.8, pp. 35–36; catalog DOI 10.1287/msom.2020.0925.

import Definitions.Def_FreemiumActions_Threshold_ThresholdPolicy

namespace FreemiumActions.Threshold

theorem theorem_2 {N : ℕ} (d : Data N) (h : Assumptions17 d) :
    ∃ y : Policy N, IsOptimal d y ∧ IsThreshold y := by sorry

end FreemiumActions.Threshold
