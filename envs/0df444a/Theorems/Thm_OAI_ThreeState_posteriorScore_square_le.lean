-- Prove2me | Theorems.Thm_OAI_ThreeState_posteriorScore_square_le
-- name    : OAI.ThreeState.posteriorScore_square_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:47:13.422046+00:00
-- url     : https://prove2.me/theorems/0e5bab36-d070-4051-a65d-0836add1e03d
-- title:
--   The squared posterior score is at most twelve times the posterior total variation
-- statement:
--   Let $\alpha$ be a type and $P=(P_0,P_1,P_2)$ a family of discrete probability distributions on $\alpha$, indexed by a spin $i\in\{0,1,2\}$. Put a uniform prior on the spin. The marginal law of the observation is $\bar P=\frac13(P_0+P_1+P_2)$, and for $y\in\alpha$ the posterior probability of spin $i$ is
--   $$
--   \pi(y,i)=\begin{cases}\dfrac{P_i(y)}{3\bar P(y)}, & \bar P(y)\neq0,\\ \dfrac13, & \bar P(y)=0.\end{cases}
--   $$
--   For $y\in\alpha$ define the posterior total variation from uniform and the posterior score of spin $0$:
--   $$
--   T(y)=\frac12\sum_{i=0}^{2}\Bigl|\pi(y,i)-\frac13\Bigr|,\qquad \rho(y)=3\,\pi(y,0)-1 .
--   $$
--   Then for every $y\in\alpha$,
--   $$
--   \rho(y)^2\le 12\,T(y).
--   $$
--
--   Averaging over $y\sim\bar P$ bounds the second moment of the posterior score by $12$ times the posterior advantage $\mathbb{E}_{\bar P}[T]$. This is the step that turns a correlation estimate for $\rho$ into a lower bound on the advantage.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/Supercritical.lean#L238-L253

import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations
import Definitions.Def_OAI_Probability_ThreeState_Messages
import Definitions.Def_OAI_Probability_ThreeState_Observation
import Definitions.Def_OAI_Probability_ThreeState_Update
import Definitions.Def_OAI_Probability_ThreeState_RadialMoments
import Definitions.Def_OAI_Probability_ThreeState_RadialDerivatives
import Definitions.Def_OAI_Probability_ThreeState_PosteriorMoments
import Definitions.Def_OAI_Probability_ThreeState_PoissonCritical
import Definitions.Def_OAI_Probability_ThreeState_Supercritical

open OAI OAI.ThreeState

theorem OAI.ThreeState.posteriorScore_square_le {α : Type*} (law : Spin → PMF α) (y : α) :
    (posteriorScore law y)^2 ≤ 12*posteriorTV law y := by sorry
