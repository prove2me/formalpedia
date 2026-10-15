-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_Law_heavy_mass_uniformOn
-- name    : OAI.ThorpCompatibility.Law.heavy_mass_uniformOn
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:07:55.658808+00:00
-- url     : https://prove2.me/theorems/3dc74de2-f87e-4e29-82ba-ffac2a16d823
-- title:
--   Heavy points of a law supported on a finite set carry mass controlled by its entropy deficit
-- statement:
--   Let $P$ be a probability law on a finite set $\Omega$, and let $s\subseteq\Omega$ be a nonempty set that carries all of the mass of $P$, i.e. $P(x)=0$ for $x\notin s$. Write $\mathrm{Ent}(P)=-\sum_xP(x)\log P(x)$ for the Shannon entropy. Then for every $H>0$,
--   $$
--   (\log H-1)\;P\Big(\Big\{x\in\Omega:\ P(x)>\frac{H}{|s|}\Big\}\Big)\le\log|s|-\mathrm{Ent}(P).
--   $$
--
--   The set on the left consists of the heavy points, whose probability exceeds $H$ times the uniform probability $1/|s|$ on $s$. For $H>e$ the theorem says that heavy points carry mass at most $(\log|s|-\mathrm{Ent}(P))/(\log H-1)$, so they can carry substantial mass only if the entropy of $P$ falls well short of its maximum $\log|s|$. It is applied to the conditional law of a column entry $c_k(i)$ given $c_k(0),\dots,c_k(i-1)$, which lives on the $A-i$ values not yet used, to bound the heavy mass of the entry by its entropy deficit.
--
--   **Formalization Note** $P$ is a `Law α`, $s$ is a nonempty `Finset α`, and $P(\{\dots\})$ is `P.prob` of the predicate `fun a => H / s.card < P.mass a`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/UniformSupport.lean#L40-L58

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

open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α : Type*} [Fintype α]

theorem OAI.ThorpCompatibility.Law.heavy_mass_uniformOn (P : Law α) (s : Finset α) (hs : s.Nonempty)
    (hz : ∀ a, a ∉ s → P.mass a = 0) {H : ℝ} (hH : 0 < H) :
    (Real.log H - 1) * P.prob (fun a => H / (s.card : ℝ) < P.mass a) ≤
      Real.log (s.card : ℝ) - P.entropy := by sorry
