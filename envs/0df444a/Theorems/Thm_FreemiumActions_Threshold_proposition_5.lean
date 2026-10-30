-- Prove2me | Theorems.Thm_FreemiumActions_Threshold_proposition_5
-- name    : FreemiumActions.Threshold.proposition_5
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T09:00:41.324405+00:00
-- url     : https://prove2.me/theorems/a3f72da5-7e79-4368-ab6d-9fbf8ed63146
-- title:
--   Proposition 5 — persistence of negative local effects
-- statement:
--   Let $N\ge0$ and $E=\{0,\ldots,N\}$. The publisher chooses a deterministic stationary policy $y:E\to\{0,1\}$. At each level the player probabilities satisfy $p_M+p_I+p_Q=q_M+q_Q=1$, with all probabilities and $\alpha$ in $[0,1]$. Removing the offer gives $q_M=p_M+\alpha p_I$ and $q_Q=p_Q+(1-\alpha)p_I$. Conditional on action $a\in\{M,I\}$ the player advances one level with constant probability $\tau_a\in[0,1]$ or stays, and stays at level $N$ if already there; quitting is absorbing. Assume $p_M,q_M,\alpha$ are nondecreasing, $p_Q,q_Q,p_I$ nonincreasing, both quitting probabilities strictly positive, $\tau_I<\tau_M$, and $0\le\mu_I<\mu_M$. The immediate revenues are $r(e,1)=p_M(e)\mu_M+p_I(e)\mu_I$ and $r(e,0)=q_M(e)\mu_M$, with zero revenue after quitting. Let $n_y(e,j)=\sum_{t\ge0}(S_y^t)_{e,j}$ and $W_y(e)=\sum_j n_y(e,j)r(j,y(j))$. These are Assumptions 1–4 with the standing probability and revenue conventions.
--
--   Also assume $\alpha(N)=1$ and $\alpha(e+1)-\alpha(e)>q_M(e+1)-q_M(e)$ on every adjacent pair. Fix a single policy $y$ for all local switches. Let $y_b^1,y_b^2$ remove and offer at $b$, respectively, and otherwise equal $y$. Write $\Delta n(e\mid b)=n_{y_b^2}(b,e)-n_{y_b^1}(b,e)$ and $C(b)=n_{y_b^2}(b,b)r(b,1)-n_{y_b^1}(b,b)r(b,0)$. The source asserts both:
--   $$\Delta n(e\mid b)<0\ \Longrightarrow\ \Delta n(e\mid b')<0\quad\text{for every }e,b,b'\in E\text{ with }b'\ge b,$$
--   $$C(b)<0\ \Longrightarrow\ C(b')<0\quad\text{for every }b,b'\in E\text{ with }b'\ge b.$$
--   The first clause includes $b'=e$ and $b'>e$; the second includes $b'=N$. These are the printed claims; counterexamples to both clauses are recorded separately.
--
--   Differences from the source:
--   - encoding: engagement levels 0 through N, quit state −1 and controls 0 or 1 → Fin (N+1), Option with none for quitting, and Bool controls; reason: order-preserving state labels and true = offer; N=0 is retained
--   - reading: increase, decrease and increasing in Assumption 3 → weak monotonicity, with quitting positivity and tauM > tauI still strict; reason: the appendix uses nondecreasing and nonincreasing comparisons
--   - encoding: earns revenue, with muI < muM in Assumption 4 → 0 ≤ muI < muM; reason: makes the model’s implicit nonnegative-revenue convention explicit without normalizing either revenue
--   - encoding: real expected infinite-horizon total reward and visit counts → nonnegative infinite sums in ENNReal; policy values are finite sums of visits times rewards; reason: positive quitting on the finite state set makes these values finite; no truncation, discount or conversion of an infinite value to zero is used
--   - reading: Assumption 6 says all e in E although e+1 is undefined at N → all adjacent pairs e,f in E with f=e+1; reason: states precisely the domain where the printed expression is defined
--   - encoding: signed real differences of finite visits and current revenues → differences after embedding ENNReal quantities in EReal; reason: all terms are finite under positive quitting; this preserves negative effects without truncated nonnegative subtraction
-- source:
--   Sheng, Ryan and Nagarajan, Incentivized actions in freemium games, supplied source.pdf dated October 8, 2016, §5, Proposition 5, p. 19 (PDF p. 19); A.7, pp. 34–35; catalog DOI 10.1287/msom.2020.0925.

import Definitions.Def_FreemiumActions_Threshold_Effects

namespace FreemiumActions.Threshold

theorem proposition_5 {N : ℕ} (d : Data N) (h : Assumptions16 d)
    (y : Policy N) :
    (∀ e b : Level N, deltaVisits d y e b < 0 →
      ∀ b' : Level N, b ≤ b' → deltaVisits d y e b' < 0) ∧
    (∀ b : Level N, currentBenefit d y b < 0 →
      ∀ b' : Level N, b ≤ b' → currentBenefit d y b' < 0) := by sorry

end FreemiumActions.Threshold
