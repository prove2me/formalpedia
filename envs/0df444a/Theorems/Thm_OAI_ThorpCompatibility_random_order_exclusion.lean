-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_random_order_exclusion
-- name    : OAI.ThorpCompatibility.random_order_exclusion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:51:56.633761+00:00
-- url     : https://prove2.me/theorems/72eee9af-f0e1-4f38-812f-e25ff5558379
-- title:
--   Expected surprisal of the not-yet-excluded mass under a uniformly random order
-- statement:
--   Let $D\ge2$, let $S_D$ be the group of permutations of $[D]=\{0,1,\dots,D-1\}$, and let $e$ be uniformly random in $S_D$, viewed as a random ordering in which item $l\in[D]$ has rank $e(l)$. Let $\mathcal B$ be a finite set, $B$ a probability distribution on $\mathcal B$, $f:\mathcal B\to[D]$ a labelling and $k\in[D]$, and assume that
--   $$
--   \alpha:=B\big(\{b\in\mathcal B:\ f(b)=k\}\big)>0 .
--   $$
--   For $e\in S_D$ let $F(e)=B\big(\{b:\ e(k)\le e(f(b))\}\big)$ be the $B$-mass of the objects whose item is not ranked strictly before $k$. Then
--
--   $$
--   1-\frac{1+\log D}{D}-\alpha\,(1+\log D)\;\le\;\mathbb E_{e\sim\mathrm{Unif}(S_D)}\big[-\log F(e)\big].
--   $$
--
--   Thus, when the mass $\alpha$ attached to $k$ itself is small, discarding the objects whose item comes before $k$ costs on average almost one unit of surprisal, up to an error $\frac{1+\log D}{D}+\alpha(1+\log D)$. In the entropy analysis of compatible grids, $B$ is a restricted prediction law for a column entry, $f$ assigns to each candidate value the column that produces it, and $F(e)$ is the predicted probability that the value is still allowed when the columns are exposed in the order $e$; the lemma bounds the expected exclusion cost $-\log F(e)$ from below.
--
--   **Formalization Note** The logarithm is applied to $F(e)\ge\alpha>0$, so no convention for $\log 0$ is involved.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/RandomExclusion.lean#L11-L48

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem OAI.ThorpCompatibility.random_order_exclusion {β : Type*} [Fintype β] {D : ℕ} (hD : 2 ≤ D)
    (B : Law β) (f : β → Fin D) (k : Fin D)
    (hα : 0 < B.prob (fun b => f b = k)) :
    1 - (1 + Real.log (D : ℝ)) / (D : ℝ) -
        B.prob (fun b => f b = k) * (1 + Real.log (D : ℝ)) ≤
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean
        (fun e => -Real.log (B.prob (fun b => e k ≤ e (f b)))) := by sorry
