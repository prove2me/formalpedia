-- Prove2me | Theorems.Thm_GreedWorks_OnlineTime_theorem_4
-- name    : GreedWorks.OnlineTime.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:07:39.065851+00:00
-- url     : https://prove2.me/theorems/9e63fe29-f85d-455b-aa1d-15301fa44f98
-- title:
--   Theorem 4, p. 18 — the online-time greedy policy has performance guarantee (7.216 + 3.608∆)h(∆)
-- statement:
--   Consider online scheduling of stochastic jobs with integer release dates on unrelated machines: job $j$ arrives at time $r_j$, has weight $w_j\ge0$, and has processing time $P_{ij}$ (integer valued, mean $\mathbb E[P_{ij}]\ge1$, finite variance) on each eligible machine $i$; processing times of different jobs are independent, and every squared coefficient of variation is at most $\Delta$. Let $(m,s)$ be an outcome of the deterministic online-time greedy algorithm with $c=\frac23$ run on the means $\mathbb E[P_{ij}]$, and let $\mathsf{ALG}=\mathbb E[\sum_jw_jC_j]$ be the expected total weighted completion time of the greedy policy for stochastic processing times (assignment $m$, nominal order on each machine, no job before its nominal start). Then for every admissible (feasible, nonanticipatory) policy $\Pi$,
--   $$\mathsf{ALG}\;\le\;(7.216+3.608\,\Delta)\,h(\Delta)\;\mathbb E\Big[\sum_jw_jC^\Pi_j\Big],\qquad h(\Delta)=\begin{cases}1+\frac{\sqrt\Delta}2,&\Delta\le1,\\[2pt]1+\frac{\Delta}{\Delta+1},&\Delta\ge1,\end{cases}$$
--   that is, $\mathsf{ALG}\le(7.216+3.608\Delta)h(\Delta)\,\mathsf{OPT}$.
--
--   This is the paper's main result for the online-time model; for deterministic processing times ($\Delta=0$) it gives the competitive ratio $7.216$ of Theorem 3.
--
--   **Formalization Note** $\mathsf{OPT}$ is replaced by an inequality against every admissible comparator, which implies the page's bound and is equivalent to it when an optimal policy exists. Comparators know all jobs and distributions in advance, choose machines and real start times freely subject to nonanticipation, and must have integrable completion times. The statement holds for every tie-breaking of the greedy algorithm. Added relative to the page: $w_j\ge0$ and integer release dates (the paper's time-indexed analysis uses integer slots; see the Model definition).
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 18, Theorem 4

import Mathlib
import Definitions.Def_GreedWorks_OnlineTime_Model
import Definitions.Def_GreedWorks_OnlineTime_Greedy
import Definitions.Def_GreedWorks_OnlineTime_StochasticGreedy

namespace GreedWorks.OnlineTime

/-- Theorem 4 (p. 18). In the online-time model with stochastic processing times on unrelated
machines, let `(m, s)` be an outcome of the deterministic greedy algorithm with `c = 2/3` run on
the means `p_ij = 𝔼[P_ij]`, and let the stochastic greedy policy GreedWorks.OnlineList.start each job no earlier than
its nominal GreedWorks.OnlineList.start and in nominal order on its GreedWorks.OnlineList.machine. Its expected total weighted GreedWorks.OnlineList.completion
time satisfies `ALG ≤ (7.216 + 3.608 Δ) h(Δ) · 𝔼[Σ_j w_j C^Π_j]` for every admissible
(feasible, nonanticipatory) policy `Π`; in particular `ALG ≤ (7.216 + 3.608 Δ) h(Δ) OPT`. -/
theorem theorem_4 {M : Type*} [Fintype M] [Nonempty M] {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (I : StochasticInstance M n Ω) (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy (2 / 3) I.release (mean I) I.weight I.eligible m s)
    (pol : GreedWorks.OnlineList.Policy M n) (hpol : IsAdmissible I pol) :
    stochValue I m s ≤ (7.216 + 3.608 * I.Delta) * hFactor I.Delta * policyCost I pol := by sorry

end GreedWorks.OnlineTime
