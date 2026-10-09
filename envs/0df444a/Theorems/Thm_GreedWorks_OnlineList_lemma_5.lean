-- Prove2me | Theorems.Thm_GreedWorks_OnlineList_lemma_5
-- name    : GreedWorks.OnlineList.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:14:29.959901+00:00
-- url     : https://prove2.me/theorems/5489d961-8ff4-43f3-9a62-9be891f67a62
-- title:
--   Lemma 5, p. 10 — speed-scaled variables are dual-feasible
-- statement:
--   Take any integer speed factor $f\ge2$. Run the greedy assignment cost and nominal unfinished-weight definitions with all mean processing times divided by $f$, giving $\alpha^f$ and $\beta^f$. Then the scaled pair is feasible for the dual $(D)$ of the original, unscaled instance:
--
--   $$\left(\alpha^f,\frac1f\beta^f\right)\in(D).$$
--
--   The definitions compute the quantities on the scaled means themselves. This feasible dual point is the one used to obtain the competitive ratio.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 10, Lemma 5

import Mathlib
import Definitions.Def_GreedWorks_OnlineList_Model
import Definitions.Def_GreedWorks_OnlineList_Greedy
import Definitions.Def_GreedWorks_OnlineList_LP

namespace GreedWorks.OnlineList

/-- Gupta et al., Lemma 5, p. 10: the scaled-instance dual variables give
a feasible dual point for the original instance when the speed is at least two. -/
theorem lemma_5 {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M] (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (m : Fin n → M) (hm : IsGreedy I m)
    (f : ℕ) (hf : 2 ≤ f) :
    IsDualFeasible I (alphaFast I m f) (fun i s => betaFast I m f i s / (f : ℝ)) := by sorry

end GreedWorks.OnlineList
