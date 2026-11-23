-- Prove2me | Theorems.Thm_GreedWorks_OnlineList_Supplement_theorem_3
-- name    : GreedWorks.OnlineList.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:55:18.22488+00:00
-- url     : https://prove2.me/theorems/376c9ea5-8c2d-4330-85b6-a4d052afde29
-- title:
--   Theorem 3, p. 13 — deterministic online-time greedy with release dates is 7.216-competitive
-- statement:
--   Consider the **online-time model** of scheduling on a finite nonempty set $M$ of unrelated machines with **deterministic** processing times: job $j=1,\dots,n$ is released at time $r_j\ge0$ (indexed so that $r_j\le r_k$ for $j<k$), has weight $w_j\ge0$ and processing time $p_{ij}\ge1$ on every machine $i$ on which it may run. The **greedy algorithm** of §6.1 with parameter $c=2/3$ uses the modified release dates $r_{ij}=\max\{r_j,c\,p_{ij}\}$; at time $r_j$ it assigns job $j$ to an eligible machine minimizing $\mathrm{cost}(j\to i)$ of Definition 4 (ties arbitrary), and each machine, whenever idle, starts among its assigned and available jobs ($r_{ik}\le t$) one of largest ratio $w_k/p_{ik}$. Let $(m,s)$ be any outcome (assignment and start times) and $\mathrm{ALG}=\sum_j w_j(s_j+p_{m(j)j})$.
--
--   Then for every admissible policy $\Pi$ (feasible, never starting a job before its release date, nonanticipatory, possibly choosing machines adaptively)
--
--   $$
--   \mathrm{ALG}\le 7.216\;\mathbb E\Big[\sum_j w_jC^{\Pi}_j\Big],\qquad\text{hence}\quad\mathrm{ALG}\le 7.216\,\mathrm{OPT}.
--   $$
--
--   The deterministic algorithm is the building block of the stochastic online-time policy of §6.3: there it is run on the expected processing times to produce the nominal schedule, and Theorem 4 extends the bound to $(7.216+3.608\Delta)h(\Delta)$.
--
--   **Formalization Note** Instances, the greedy rule (`GreedWorks.OnlineTime.IsGreedy` with $c=2/3$, run on $p_{ij}=\mathbb E[P_{ij}]$), its objective and the admissible comparators are the published definitions of the sibling mission; a deterministic instance is one whose processing times are almost surely constant on eligible pairs, so $\mathbb E[P_{ij}]=p_{ij}$. The statement holds for every outcome $(m,s)$, i.e. for every way of breaking ties. $\mathrm{OPT}$ is replaced by "every admissible policy".
--
--   Differences from the source:
--   - encoding: ALG ≤ 7.216·OPT, with OPT the optimum over nonanticipatory policies → ALG ≤ 7.216·𝔼[Σ_j w_j C^Π_j] for every admissible Π; reason: implies the printed bound and is equivalent to it when an optimal policy exists; admissible = feasible (start ≥ release date), nonanticipatory, integrable completion times (published sibling model).
--   - encoding: deterministic processing times p_ij and release dates r_j → a stochastic instance of the published online-time model whose processing times are almost surely equal to a natural number on eligible pairs, with natural-number release dates; ALG is the objective of the algorithm run on p_ij = E[P_ij]; reason: the paper's standing assumptions (p. 5: processing times integer valued, p. 6: E[P_ij] ≥ 1 by scaling) and the proof's own convention (p. 14: "all job sizes and release times are integer multiples of f, which can be achieved by scaling"); the ratio is invariant under scaling time, and the published model fixes the same convention.
--   - reading: "the greedy algorithm" (parameter c unspecified in the statement) → the algorithm of §6.1 with c = 2/3; reason: the proof of Theorem 3 sets c = 2/3 (p. 14), and the constant 7.216 is for that choice.
--   - encoding: weights w_j → weights w_j ≥ 0; reason: implicit on the page and used by every argument; a field of the published instance.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 13, Theorem 3, with its proof on pp. 13–15 (c = 2/3, a = 32/23, b = 16/3, f = 23/6, p. 14)

import Mathlib
import Definitions.Def_GreedWorks_OnlineTime_Model
import Definitions.Def_GreedWorks_OnlineTime_Greedy
import Definitions.Def_GreedWorks_OnlineList_Supplement_Deterministic

namespace GreedWorks.OnlineList.Supplement

/-- Theorem 3 (p. 13). For deterministic processing times with release dates, every outcome
`(m, s)` of the online-time greedy algorithm of §6.1 with parameter `c = 2/3`, run on the
processing times `p_ij = 𝔼[P_ij]`, has total weighted completion time
`Σ_j w_j C_j ≤ 7.216 · 𝔼[Σ_j w_j C^Π_j]` for every admissible policy `Π`; that is,
`ALG ≤ 7.216 OPT`. -/
theorem theorem_3 {M : Type*} [Fintype M] [Nonempty M] {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (I : GreedWorks.OnlineTime.StochasticInstance M n Ω)
    (hdet : IsDeterministicTime I) (m : Fin n → M) (s : Fin n → ℝ)
    (hG : GreedWorks.OnlineTime.IsGreedy (2 / 3) I.release (GreedWorks.OnlineTime.mean I)
      I.weight I.eligible m s)
    (pol : GreedWorks.OnlineList.Policy M n) (hpol : GreedWorks.OnlineTime.IsAdmissible I pol) :
    GreedWorks.OnlineTime.nominalValue (GreedWorks.OnlineTime.mean I) I.weight m s ≤
      7.216 * GreedWorks.OnlineTime.policyCost I pol := by sorry

end GreedWorks.OnlineList.Supplement
