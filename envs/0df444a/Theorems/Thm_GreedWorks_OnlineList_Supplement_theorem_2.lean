-- Prove2me | Theorems.Thm_GreedWorks_OnlineList_Supplement_theorem_2
-- name    : GreedWorks.OnlineList.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:54:28.633646+00:00
-- url     : https://prove2.me/theorems/00ab2f7f-fe4a-4dbc-866a-266acbacb9df
-- title:
--   Theorem 2, p. 11 — deterministic online-list greedy is 4-competitive, and the ratio 4 is tight
-- statement:
--   Consider the **online-list model** of scheduling on a finite nonempty set $M$ of unrelated machines with **deterministic** processing times: jobs $j=1,\dots,n$ are presented one by one in this order, each with weight $w_j\ge0$ and processing time $p_{ij}\in\{1,2,\dots\}$ on every machine $i$ on which it may run (on the other machines $p_{ij}=\infty$). The **greedy algorithm** assigns each arriving job to a machine $m(j)$ minimizing the increase in total weighted completion time caused by inserting $j$ into the WSPT order of the jobs already assigned there (machine ties broken arbitrarily), and each machine processes its jobs in WSPT order, ties by arrival. Its objective is $\mathrm{ALG}=\sum_j w_jC_j$. $\mathrm{OPT}$ is the least expected total weighted completion time of a nonanticipatory policy that knows all jobs in advance and may choose machines at any time.
--
--   1. **Upper bound.** For every deterministic instance, every run $m$ of the greedy algorithm and every admissible policy $\Pi$,
--
--   $$
--   \mathrm{ALG}\le 4\,\mathbb E\Big[\sum_j w_jC^{\Pi}_j\Big],\qquad\text{hence}\quad \mathrm{ALG}\le 4\,\mathrm{OPT}.
--   $$
--
--   2. **Tightness.** For every $\varepsilon>0$ there are a deterministic instance, a run $m$ of the greedy algorithm (with some admissible way of breaking machine ties) and an admissible policy $\Pi$ with $\mathbb E[\sum_j w_jC^\Pi_j]>0$ and
--
--   $$
--   (4-\varepsilon)\,\mathbb E\Big[\sum_j w_jC^{\Pi}_j\Big]\le \mathrm{ALG},\qquad\text{hence}\quad \mathrm{ALG}\ge(4-\varepsilon)\,\mathrm{OPT}.
--   $$
--
--   The theorem shows that the ratio $4+2\Delta$ of Theorem 1 cannot be improved at $\Delta=0$ for the greedy algorithm: its analysis is exact in the deterministic case.
--
--   **Formalization Note** Instances, the greedy rule (every eligible minimizer of the instantaneous cost, WSEPT order with index tie-breaking, which is WSPT here), ALG and the admissible (feasible, nonanticipatory, integrable) comparator policies are the published definitions of the base mission; a deterministic instance is a stochastic one whose processing times are almost surely constant on eligible pairs. $\mathrm{OPT}$ is not written as an infimum: the upper bound holds against every admissible policy, and the lower bound exhibits an admissible policy, whose cost bounds $\mathrm{OPT}$ from above. Positivity of that cost excludes the trivial instance with zero weights.
--
--   Differences from the source:
--   - encoding: ALG ≤ 4·OPT, with OPT the optimum over nonanticipatory policies → ALG ≤ 4·𝔼[Σ_j w_j C^Π_j] for every admissible Π; reason: implies the printed bound and is equivalent to it when an optimal policy exists; admissible = feasible, nonanticipatory, integrable completion times (published base model).
--   - reading: "there is a tight lower bound of 4" → for every ε > 0 there exist a deterministic instance, a greedy assignment satisfying IsGreedy (some admissible tie-breaking) and an admissible Π with positive cost and (4 − ε)·cost(Π) ≤ ALG; reason: the proof lets k → ∞ over the instances I_k of [9] and fixes the tie-breaking "in favour of lower machine index", which is one of the runs the greedy rule allows; cost(Π) ≥ OPT turns this into ALG ≥ (4 − ε)·OPT, and positivity excludes the trivial zero-weight instance.
--   - encoding: deterministic processing times p_ij, with p_ij = ∞ on forbidden pairs → a stochastic instance of the published model whose processing times are almost surely equal to a natural number on every eligible pair; forbidden pairs are ineligible; reason: the paper's deterministic problem is the special case of its model (p. 12: p_ij := E[P_ij]); integer values with p_ij ≥ 1 are the paper's standing assumption (pp. 5–6, "discrete and integer valued", E[P_ij] ≥ 1 by scaling), and the ratio is invariant under scaling time.
--   - encoding: weights w_j → weights w_j ≥ 0; reason: implicit on the page and used by every argument; a field of the published instance.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 11, Theorem 2, with its proof on pp. 11–12

import Mathlib
import Definitions.Def_GreedWorks_OnlineList_Model
import Definitions.Def_GreedWorks_OnlineList_Greedy
import Definitions.Def_GreedWorks_OnlineList_Supplement_Deterministic

namespace GreedWorks.OnlineList.Supplement

universe u v

open GreedWorks.OnlineList

/-- Theorem 2 (p. 11). For deterministic processing times, the online-list greedy algorithm
(greedy assignment, WSPT sequencing) is 4-competitive, and 4 is tight.

(1) Upper bound: on every deterministic instance, every greedy assignment `m` satisfies
`ALG ≤ 4 · 𝔼[Σ_j w_j C^Π_j]` for every admissible policy `Π`.

(2) Lower bound: for every `ε > 0` there are a deterministic instance, a greedy assignment `m`
(a run of the algorithm with some admissible tie-breaking) and an admissible policy `Π` of
positive cost with `(4 − ε) · 𝔼[Σ_j w_j C^Π_j] ≤ ALG`, so that `ALG ≥ (4 − ε) OPT`. -/
theorem theorem_2 :
    (∀ (M : Type u) [Fintype M] [DecidableEq M] [Nonempty M] (n : ℕ)
        (Ω : Type v) [MeasurableSpace Ω] (I : StochasticInstance M n Ω),
        IsDeterministic I → ∀ m : Fin n → M, IsGreedy I m →
        ∀ pol : Policy M n, IsAdmissible I pol →
          algorithmCost I m ≤ 4 * comparatorCost I pol) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ (M : Type) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M) (n : ℕ)
        (Ω : Type) (_ : MeasurableSpace Ω) (I : StochasticInstance M n Ω)
        (m : Fin n → M) (pol : Policy M n),
        IsDeterministic I ∧ IsGreedy I m ∧ IsAdmissible I pol ∧
          0 < comparatorCost I pol ∧
          (4 - ε) * comparatorCost I pol ≤ algorithmCost I m) := by sorry

end GreedWorks.OnlineList.Supplement
