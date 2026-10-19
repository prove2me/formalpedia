-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_observableEntropy_mixture_joint
-- name    : OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_joint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:05:57.233206+00:00
-- url     : https://prove2.me/theorems/5ca22b5c-a714-4634-81e3-81c80c4eba3f
-- title:
--   Joint entropy of a mixture and its index
-- statement:
--   Let $t,s$ be finite sets, $w$ weights on $t$, and $p_i$ weights on $s$ summing to $1$ for each $i\in t$. Under the product weights $w_ip_i(a)$ on $t\times s$, the observable $(i,a)\mapsto(i,f(a))$ has entropy
--   $$
--   H\bigl(i,f(a)\bigr)=H(t,w)+\sum_{i\in t}w_i\,H_s\bigl(f;p_i\bigr).
--   $$
--
--   This is the chain rule for revealing the mixture index together with the observable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean#L796-L830

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_joint {ι : Type uι} {α : Type uα} {β : Type uβ} [DecidableEq ι] [DecidableEq β]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β)
    (hp : ∀ i ∈ t, ∑ a ∈ s, p i a = 1) :
    observableEntropy (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => (ia.1,f ia.2)) =
      entropy t w + ∑ i ∈ t, w i*observableEntropy s (p i) f := by sorry
