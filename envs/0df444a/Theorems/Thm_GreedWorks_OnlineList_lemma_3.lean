-- Prove2me | Theorems.Thm_GreedWorks_OnlineList_lemma_3
-- name    : GreedWorks.OnlineList.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:14:48.334929+00:00
-- url     : https://prove2.me/theorems/eafb5d93-528b-4a3e-aa67-14dbf77f71ee
-- title:
--   Lemma 3, p. 9 — greedy variables are dual-feasible after halving
-- statement:
--   For any eligible-minimum greedy assignment $m$, define $\alpha_j$ as the instantaneous increase in expected weighted completion cost when $j$ is assigned, and $\beta_{is}$ as the total weight of jobs assigned to machine $i$ and nominally unfinished at integer time $s$. Then
--
--   $$\left(\frac\alpha2,\frac\beta2\right)\text{ is feasible for the dual }(D).$$
--
--   In particular, the dual inequalities hold for every eligible machine-job pair and every integer slot, $\beta/2$ is nonnegative, and each $\beta_i/2$ series is summable. This is the first dual-fitting milestone.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 9, Lemma 3

import Mathlib
import Definitions.Def_GreedWorks_OnlineList_Model
import Definitions.Def_GreedWorks_OnlineList_Greedy
import Definitions.Def_GreedWorks_OnlineList_LP

namespace GreedWorks.OnlineList

/-- Gupta et al., Lemma 3, p. 9: half of the greedy dual-fitting variables
form a feasible point of (D). -/
theorem lemma_3 {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M] (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (m : Fin n → M) (hm : IsGreedy I m) :
    IsDualFeasible I (fun j => alpha I m j / 2) (fun i s => beta I m i s / 2) := by sorry

end GreedWorks.OnlineList
