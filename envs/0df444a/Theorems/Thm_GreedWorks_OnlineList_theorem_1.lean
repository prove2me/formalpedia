-- Prove2me | Theorems.Thm_GreedWorks_OnlineList_theorem_1
-- name    : GreedWorks.OnlineList.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:13:09.298428+00:00
-- url     : https://prove2.me/theorems/9048a63e-fa5c-456c-aaa8-a57783535b15
-- title:
--   Theorem 1, p. 11 — greedy WSEPT is $(4+2\Delta)$-competitive
-- statement:
--   Consider any stochastic unrelated-machine online-list instance with eligible machine-job pairs, independent job-time vectors, finite second moments and eligible means at least one. Let $\Delta$ bound every eligible squared coefficient of variation. For every assignment $m$ that sends each arriving job to an eligible machine of minimum instantaneous expected cost, sequence each machine's assigned jobs by nonincreasing weight-to-mean ratio, breaking equal ratios by job index. Let $\mathrm{ALG}$ be the expected weighted completion cost of this realized schedule. For every feasible nonanticipatory policy $\Pi$ with integrable completion times,
--
--   $$\mathrm{ALG}\le(4+2\Delta)\,\mathbb E\!\left[\sum_j w_jC_j^\Pi\right].$$
--
--   Thus the greedy online-list algorithm has the paper's $(4+2\Delta)$ performance guarantee against an optimal policy that knows all job distributions in advance but not their realizations. **Formalization Note** Weights are nonnegative, as implicitly required by the paper. The theorem permits forbidden machine-job pairs and arbitrary dependence between machines for the same job. Quantification over every admissible comparator expresses the bound against $\mathrm{OPT}$ without a potentially junk-valued infimum.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 11, Theorem 1

import Mathlib
import Definitions.Def_GreedWorks_OnlineList_Model
import Definitions.Def_GreedWorks_OnlineList_Greedy

namespace GreedWorks.OnlineList

/-- Gupta et al., Theorem 1, p. 11: every greedy assignment with WSEPT
sequencing is `(4 + 2Δ)`-competitive against every admissible nonanticipatory
policy, which may choose machines adaptively. -/
theorem theorem_1 {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M] (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (m : Fin n → M) (hm : IsGreedy I m)
    (pol : Policy M n) (hpol : IsAdmissible I pol) :
    algorithmCost I m ≤ (4 + 2 * I.Delta) * comparatorCost I pol := by sorry

end GreedWorks.OnlineList
