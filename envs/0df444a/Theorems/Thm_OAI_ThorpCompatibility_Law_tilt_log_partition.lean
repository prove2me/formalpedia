-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_Law_tilt_log_partition
-- name    : OAI.ThorpCompatibility.Law.tilt_log_partition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:14:52.517462+00:00
-- url     : https://prove2.me/theorems/ee40cd2b-7f91-4724-bcd3-cd2e91c6aa12
-- title:
--   Log-partition identity for the law proportional to a nonnegative weight
-- statement:
--   Let $\Omega$ be a nonempty finite set and $a:\Omega\to[0,\infty)$ a nonnegative weight with $Z=\sum_{x\in\Omega}a(x)>0$. Let $P_a$ be the tilted law $P_a(x)=a(x)/Z$, and let $\Delta(P)=\log|\Omega|-\mathrm{Ent}(P)$ denote the uniform deficit, where $\mathrm{Ent}(P)=-\sum_xP(x)\log P(x)$. Then
--   $$
--   \mathbb{E}_{P_a}[\log a]-\Delta(P_a)=\log\Big(\frac1{|\Omega|}\sum_{x\in\Omega}a(x)\Big).
--   $$
--
--   The right side is the logarithm of the uniform mean of $a$, a normalized partition function. The identity shows that the tilted law attains equality in the Gibbs variational inequality $\mathbb{E}_P[\log a]-\Delta(P)\le\log\big(\frac1{|\Omega|}\sum_xa(x)\big)$. In the weighted compatibility bound it is applied on the grid with $a$ equal to the compatibility weight $\mathbf 1[(r,c)\text{ compatible}]\prod_iw_i(r_i)\prod_kv_k(c_k)$. This rewrites the logarithm of the averaged weight as an expectation minus an entropy deficit, to which the entropy estimates then apply.
--
--   **Formalization Note** $P_a$ is `Law.tilt a ha hZ`, which takes the nonnegativity and positivity proofs as arguments, and the right side is `Real.log (uniformMean a)`. Lean's convention $\log0=0$ does not matter, since points with $a(x)=0$ have $P_a(x)=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/WeightedGibbs.lean#L69-L87

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpMoments
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyEntries
import Definitions.Def_OAI_Probability_ThorpCompatibility_ExposureEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_UniformSupport
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyColumns
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridDeficits

open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α : Type*} [Fintype α]

theorem OAI.ThorpCompatibility.Law.tilt_log_partition [Nonempty α] (a : α → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hZ : 0 < ∑ x, a x) :
    (Law.tilt a ha hZ).mean (fun x => Real.log (a x)) -
      (Law.tilt a ha hZ).uniformDeficit = Real.log (uniformMean a) := by sorry
