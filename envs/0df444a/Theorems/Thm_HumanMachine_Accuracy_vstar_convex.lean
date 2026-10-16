-- Prove2me | Theorems.Thm_HumanMachine_Accuracy_vstar_convex
-- name    : HumanMachine.Accuracy.vstar_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:23:53.893753+00:00
-- url     : https://prove2.me/theorems/b1ea542c-b476-44b5-a0e9-ee280c6570b8
-- title:
--   Proof of Proposition 1 — the optimal expected value $V^\star$ is convex in $\mu$ on $[0,1]$
-- statement:
--   Let $\lambda>0$ be the information cost. The DM's optimal expected value $V^\star(\mu)$, as a function of her prior belief $\mu$ that the state is good, is convex on $[0,1]$:
--
--   $$V^\star\big((1-t)\mu_1+t\mu_2\big)\le(1-t)V^\star(\mu_1)+tV^\star(\mu_2)\qquad\text{for all }\mu_1,\mu_2,t\in[0,1].$$
--
--   Together with Lemma 2 and Jensen's inequality this yields the value half of Proposition 1.
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), p. 33, Appendix A, proof of Proposition 1, second paragraph

import Mathlib
import Definitions.Def_HumanMachine_Accuracy_DecisionModel

namespace HumanMachine.Accuracy

/-- Proof of Proposition 1 (p. 33): for information cost `λ > 0`, the optimal expected value
`V⋆` is convex in the prior `μ` on `[0, 1]`. -/
theorem vstar_convex (lam : ℝ) (hlam : 0 < lam) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (VStar lam) := by sorry

end HumanMachine.Accuracy
