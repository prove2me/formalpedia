-- Prove2me | Theorems.Thm_GreedWorks_OnlineList_corollary_1
-- name    : GreedWorks.OnlineList.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:14:26.429066+00:00
-- url     : https://prove2.me/theorems/24266217-a4d0-46a1-9306-5fa656bc03d3
-- title:
--   Corollary 1, p. 8 — LP bound against a nonanticipatory policy
-- statement:
--   For every admissible nonanticipatory scheduling policy $\Pi$ in the online-list instance, there is a feasible point $y$ of the deterministic relaxation $(P)$ for which
--
--   $$z^P(y)\le\left(1+\frac\Delta2\right)\mathbb E\!\left[\sum_j w_jC_j^\Pi\right].$$
--
--   Consequently the optimal value of $(P)$ is at most $(1+\Delta/2)\mathrm{OPT}$. The comparator may choose its machine assignments and start times adaptively; its completion times are integrable. This is the LP comparison used by Theorem 1.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, p. 8, Corollary 1

import Mathlib
import Definitions.Def_GreedWorks_OnlineList_Model
import Definitions.Def_GreedWorks_OnlineList_LP

namespace GreedWorks.OnlineList

/-- Gupta et al., Corollary 1, p. 8: the deterministic LP lower-bounds the
fully adaptive comparator up to the coefficient-of-variation factor. -/
theorem corollary_1 {M : Type*} [Fintype M] [Nonempty M] (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) (pol : Policy M n)
    (hpol : IsAdmissible I pol) :
    ∃ y : ProcessingPoint M n,
      IsPrimalFeasible I y ∧
        primalValue I y ≤ (1 + I.Delta / 2) * comparatorCost I pol := by sorry

end GreedWorks.OnlineList
