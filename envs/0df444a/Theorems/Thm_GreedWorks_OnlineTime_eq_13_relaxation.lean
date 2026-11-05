-- Prove2me | Theorems.Thm_GreedWorks_OnlineTime_eq_13_relaxation
-- name    : GreedWorks.OnlineTime.eq_13_relaxation
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T14:25:37.894925+00:00
-- url     : https://prove2.me/theorems/c18454c6-7d3b-48c5-927e-6f0117dbbfcd
-- title:
--   (13), §6.2, p. 15 — (S_r) is a relaxation: z^{S_r} ≤ OPT for every admissible policy
-- statement:
--   Consider a stochastic unrelated-machine instance with integer release dates $r_j$, weights $w_j\ge0$, and integer-valued processing times $P_{ij}$ on eligible pairs, with means $\mathbb E[P_{ij}]\ge1$ and squared coefficients of variation $\mathbb{CV}[P_{ij}]^2$. Processing times of different jobs are independent.
--
--   The time-indexed relaxation $(S_r)$ has a variable $y_{ijs}\ge0$ for every eligible pair $(i,j)$ and every integer slot $s\ge r_j$. Its constraints are
--   $$\sum_j y_{ijs}\le1,\qquad \sum_i\sum_s\frac{y_{ijs}}{\mathbb E[P_{ij}]}=1,\qquad C^S_j\ge\sum_i\sum_s y_{ijs},$$
--   where
--   $$C^S_j=\sum_i\sum_s\Big(\frac{y_{ijs}}{\mathbb E[P_{ij}]}\big(s+\tfrac12\big)+\frac{1-\mathbb{CV}[P_{ij}]^2}{2}\,y_{ijs}\Big),$$
--   and its objective is $z^{S_r}(y)=\sum_j w_jC^S_j$.
--
--   **Claim.** $(S_r)$ is a relaxation of the stochastic scheduling problem. For every admissible policy $\Pi$ (feasible, nonanticipatory, with integrable completion times) there is a point $y$ feasible for $(S_r)$ with
--   $$z^{S_r}(y)\;\le\;\mathbb E\Big[\sum_j w_jC^\Pi_j\Big].$$
--
--   This is the second inequality $z^{S_r}\le\mathsf{OPT}$ of (13). Together with the comparison $z^{P_r}\le(1+\Delta/2)z^{S_r}$ it yields the lower bound used in the proof of Theorem 4. In the paper the natural candidate is $y_{ijs}=$ the probability that $j$ is processed on machine $i$ during $[s,s+1]$ under $\Pi$. Its validity rests on (1)–(5) of §3 and Lemma 9.
--
--   **Formalization Note** This is part (b) of the milestone `GreedWorks.OnlineTime.eq_13`, stated verbatim and without infima. Comparator policies may start jobs at real times, and the processing times are $\mathbb N$-valued. The data structures are those of the definitions `GreedWorks_OnlineTime_Model` and `GreedWorks_OnlineTime_TimeIndexedLP`.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 15, eq. (13) (second inequality), with the LP (S) of §3, pp. 6–7, eqs. (1)–(5)

import Mathlib
import Definitions.Def_GreedWorks_OnlineTime_Model
import Definitions.Def_GreedWorks_OnlineTime_TimeIndexedLP

namespace GreedWorks.OnlineTime

open MeasureTheory

/-- (13), §6.2, p. 15, second inequality `z^{S_r} ≤ OPT` (with the derivation of (S) in §3,
pp. 6–7, transferred to release dates), stated without infima: (S_r) is a relaxation — for every
admissible (feasible, nonanticipatory, integrable) policy there is a point feasible for (S_r)
whose objective value is at most the policy's expected total weighted completion time. -/
theorem eq_13_relaxation {M : Type*} [Fintype M] [Nonempty M] {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (I : StochasticInstance M n Ω) :
    ∀ pol : GreedWorks.OnlineList.Policy M n, IsAdmissible I pol →
      ∃ y, IsFeasibleS I.eligible I.release (mean I) (cvSquared I) y ∧
        valueS I.eligible (mean I) (cvSquared I) I.weight y ≤ policyCost I pol := by sorry

end GreedWorks.OnlineTime
