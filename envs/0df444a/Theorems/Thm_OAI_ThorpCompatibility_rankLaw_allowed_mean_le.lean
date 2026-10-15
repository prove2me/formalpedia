-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_rankLaw_allowed_mean_le
-- name    : OAI.ThorpCompatibility.rankLaw_allowed_mean_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T23:51:33.260249+00:00
-- url     : https://prove2.me/theorems/de08910b-cb1f-425a-bf70-d18bec11caff
-- title:
--   Expected mass of items not ranked before $k$ under a rank-conditioned random order
-- statement:
--   Let $D\ge2$, let $S_D$ be the group of permutations of $[D]=\{0,1,\dots,D-1\}$, and for $k,t\in[D]$ let $\rho_{k,t}$ be the uniform distribution on $S_D$ conditioned on $\{e(k)=t\}$. Let $\mathcal B$ be a finite set, $B$ a probability distribution on $\mathcal B$, and $f:\mathcal B\to[D]$ a labelling. Then
--
--   $$
--   \mathbb E_{e\sim\rho_{k,t}}\Big[B\big(\{b\in\mathcal B:\ e(k)\le e(f(b))\}\big)\Big]\;\le\;\frac{D-t}{D}+B\big(\{b\in\mathcal B:\ f(b)=k\}\big).
--   $$
--
--   Think of $e$ as a random ordering of $D$ items in which item $k$ has rank $t$, and of $b\sim B$ as a random object attached to the item $f(b)$. The left side is the expected probability that the item of $b$ is not ranked strictly before $k$. Under $\rho_{k,t}$ every item $l\ne k$ is ranked after $k$ with probability at most $\frac{D-t}{D}$, while objects attached to $k$ itself always count; the bound adds these two contributions.
--
--   **Formalization Note** $D-t$ is natural-number subtraction cast to $\mathbb{R}$, never truncated since $t<D$; $\rho_{k,t}$ is `rankLaw k t`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/RankAverages.lean#L117-L135

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

theorem OAI.ThorpCompatibility.rankLaw_allowed_mean_le {β : Type*} [Fintype β] {D : ℕ} (hD : 2 ≤ D)
    (B : Law β) (f : β → Fin D) (k t : Fin D) :
    (rankLaw k t).mean (fun e => B.prob (fun b => e k ≤ e (f b))) ≤
      ((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ) + B.prob (fun b => f b = k) := by sorry
