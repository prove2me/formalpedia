-- Prove2me | Theorems.Thm_GreedWorks_OnlineTime_lemma_8
-- name    : GreedWorks.OnlineTime.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:07:18.013307+00:00
-- url     : https://prove2.me/theorems/1c3caed8-6548-42d8-af4c-70158663e2c5
-- title:
--   Lemma 8, p. 18 — E[S_j] ≤ h(∆) s_j: expected start under the stochastic policy vs. nominal start
-- statement:
--   Consider a stochastic unrelated-machine instance with integer release dates and squared coefficients of variation bounded by $\Delta$. Let $(m,s)$ be the nominal schedule, an outcome of the online-time greedy algorithm with $c=\frac23$ run on the means $p_{ij}=\mathbb E[P_{ij}]$, and let $S_j$ be the start time of job $j$ under the greedy policy for stochastic processing times. Then for every job $j$
--   $$\mathbb E[S_j]\le h(\Delta)\,s_j,\qquad h(\Delta)=\begin{cases}1+\frac{\sqrt\Delta}2,&\Delta\le1,\\[2pt]1+\frac{\Delta}{\Delta+1},&\Delta\ge1.\end{cases}$$
--
--   Consequently $\mathbb E[C_j]\le h(\Delta)\,C^P_j$ for the nominal completion times $C^P_j$, so the stochastic policy loses at most the factor $h(\Delta)\le2$ against its nominal schedule.
--
--   **Formalization Note** The page writes $S_{i,j}$ for the start of job $j$ on its machine $i=m(j)$; since the assignment is deterministic, $S_{i,j}=S_j$. The nominal schedule is the goal's, with $c=\frac23$.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 18, Lemma 8

import Mathlib
import Definitions.Def_GreedWorks_OnlineTime_Model
import Definitions.Def_GreedWorks_OnlineTime_Greedy
import Definitions.Def_GreedWorks_OnlineTime_StochasticGreedy

namespace GreedWorks.OnlineTime

open MeasureTheory

/-- Lemma 8 (p. 18). Let `(m, s)` be the nominal schedule: an outcome of the online-time greedy
algorithm (parameter `c = 2/3`) run on the means `p_ij = 𝔼[P_ij]`. Under the stochastic greedy
policy of §6.3, the expected GreedWorks.OnlineList.start time of every job `j` is at most `h(Δ)` times its nominal
GreedWorks.OnlineList.start time: `𝔼[S_j] ≤ h(Δ) s_j`. -/
theorem lemma_8 {M : Type*} [Fintype M] [Nonempty M] {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (m : Fin n → M) (s : Fin n → ℝ)
    (hG : IsGreedy (2 / 3) I.release (mean I) I.weight I.eligible m s) (j : Fin n) :
    ∫ ω, stochStart m s (realize I ω) j ∂I.Pr ≤ hFactor I.Delta * s j := by sorry

end GreedWorks.OnlineTime
