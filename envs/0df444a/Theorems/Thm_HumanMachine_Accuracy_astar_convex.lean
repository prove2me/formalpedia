-- Prove2me | Theorems.Thm_HumanMachine_Accuracy_astar_convex
-- name    : HumanMachine.Accuracy.astar_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:09.856752+00:00
-- url     : https://prove2.me/theorems/a6974238-1b6a-434c-a6a3-2cc4549375cf
-- title:
--   Proof of Proposition 1 — the optimal accuracy $A^\star$ is convex in $\mu$ on $[0,1]$
-- statement:
--   Let $\lambda>0$ be the information cost. The DM's optimal accuracy $A^\star(\mu)$, as a function of her prior belief $\mu$ that the state is good, is convex on $[0,1]$:
--
--   $$A^\star\big((1-t)\mu_1+t\mu_2\big)\le(1-t)A^\star(\mu_1)+tA^\star(\mu_2)\qquad\text{for all }\mu_1,\mu_2,t\in[0,1].$$
--
--   Convexity is what turns the split of the prior by the machine's output into an accuracy gain via Jensen's inequality.
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), p. 33, Appendix A, proof of Proposition 1, first sentence

import Mathlib
import Definitions.Def_HumanMachine_Accuracy_DecisionModel

namespace HumanMachine.Accuracy

/-- Proof of Proposition 1 (p. 33): for information cost `λ > 0`, the optimal accuracy `A⋆` is
convex in the prior `μ` on `[0, 1]`. -/
theorem astar_convex (lam : ℝ) (hlam : 0 < lam) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (AStar lam) := by sorry

end HumanMachine.Accuracy
