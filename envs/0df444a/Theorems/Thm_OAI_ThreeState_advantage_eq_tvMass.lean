-- Prove2me | Theorems.Thm_OAI_ThreeState_advantage_eq_tvMass
-- name    : OAI.ThreeState.advantage_eq_tvMass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:42:24.046289+00:00
-- url     : https://prove2.me/theorems/4293060e-1750-4d2c-baf2-f6f91a566ab2
-- title:
--   Posterior advantage equals the average total variation distance to the marginal
-- statement:
--   Let $\alpha$ be a type and $P=(P_0,P_1,P_2)$ a family of discrete probability distributions on $\alpha$, indexed by a spin $i\in\{0,1,2\}$. Put a uniform prior on the spin. The marginal law of the observation is $\bar P=\frac13(P_0+P_1+P_2)$, and for $y\in\alpha$ the posterior probability of spin $i$ is
--   $$
--   \pi(y,i)=\begin{cases}\dfrac{P_i(y)}{3\bar P(y)}, & \bar P(y)\neq0,\\ \dfrac13, & \bar P(y)=0.\end{cases}
--   $$
--   The advantage of $P$ is the expected distance of the posterior from uniform,
--   $$
--   \mathrm{Adv}(P)=\sum_{y\in\alpha}\bar P(y)\cdot\frac12\sum_{i=0}^{2}\Bigl|\pi(y,i)-\frac13\Bigr| .
--   $$
--   With $d_{\mathrm{TV}}(p,q)=\frac12\sum_{y}|p(y)-q(y)|$, the theorem states
--   $$
--   \mathrm{Adv}(P)=\frac13\sum_{i=0}^{2}d_{\mathrm{TV}}\bigl(P_i,\bar P\bigr).
--   $$
--
--   This rewrites a posterior quantity as a sum of total variation distances. Total variation cannot increase when the same Markov kernel is applied to both arguments, so in this form the advantage is visibly non-increasing under further processing of the observation.
--
--   **Formalization Note** $P_i(y)$ is `mass (law i) y`, the real value of the probability mass function. The sums over $\alpha$ are real `tsum`s.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/Basic.lean#L203-L217

import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic

open OAI OAI.ThreeState

theorem OAI.ThreeState.advantage_eq_tvMass {α : Type*} (law : Spin → PMF α) :
    advantage law = (∑ i : Spin, tvMass (law i) (marginal law))/3 := by sorry
