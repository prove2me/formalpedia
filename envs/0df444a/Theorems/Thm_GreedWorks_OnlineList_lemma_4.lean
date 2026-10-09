-- Prove2me | Theorems.Thm_GreedWorks_OnlineList_lemma_4
-- name    : GreedWorks.OnlineList.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:51.352972+00:00
-- url     : https://prove2.me/theorems/adcf83e4-4b0d-4da6-9152-acbb7e16f8b1
-- title:
--   Lemma 4, p. 10 — greedy objective and dual-variable identities
-- statement:
--   For any greedy assignment and its WSEPT schedule, the algorithm's expected total weighted completion time equals the sum of its incremental assignment costs:
--
--   $$\mathrm{ALG}=\sum_j\alpha_j.$$
--
--   The paper additionally writes $\mathrm{ALG}=\sum_i\sum_{s\ge0}\beta_{is}$. This second identity is asserted here when every eligible mean processing time $\mu_{ij}$ is an integer. It relates the algorithm's objective to the dual variables used in the speed argument.
--
--   **Formalization Note** The first equality has no integer-mean condition. The second equality as printed fails for noninteger means: with one job, weight $1$, and mean $3/2$, $\mathrm{ALG}=3/2$ but $\sum_s\beta_{is}=2$. This is a disclosed correction of the source's integer-slot count, and the goal theorem retains general means.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 10, Lemma 4

import Mathlib
import Definitions.Def_GreedWorks_OnlineList_Model
import Definitions.Def_GreedWorks_OnlineList_Greedy

namespace GreedWorks.OnlineList

/-- Gupta et al., Lemma 4, p. 10.  The first equality holds as printed;
the second needs integer means because β counts whole integer time slots. -/
theorem lemma_4 {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M] (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (m : Fin n → M) (hm : IsGreedy I m) :
    algorithmCost I m = ∑ j : Fin n, alpha I m j ∧
      ((∀ i j, I.eligible i j → ∃ q : ℕ, mean I i j = q) →
        algorithmCost I m = ∑ i : M, ∑' s : ℕ, beta I m i s) := by sorry

end GreedWorks.OnlineList
