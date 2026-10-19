-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_observableEntropy_mixture_joint_general
-- name    : OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_joint_general
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:07:03.055057+00:00
-- url     : https://prove2.me/theorems/d8276226-79a0-4aab-a801-a1c253631ef6
-- title:
--   Joint entropy of a mixture with unnormalized components
-- statement:
--   Let $t,s$ be finite sets, $w$ weights on $t$ and $p_i$ weights on $s$, not necessarily normalized. Under the product weights $w_ip_i(a)$, the observable $(i,a)\mapsto(i,f(a))$ has entropy
--   $$
--   H\bigl(i,f(a)\bigr)=\sum_{i\in t}\Bigl(\Bigl(\sum_{a\in s}p_i(a)\Bigr)(-w_i\log w_i)+w_i\,H_s(f;p_i)\Bigr).
--   $$
--
--   When each $p_i$ sums to $1$ this reduces to $H(t,w)+\sum_iw_iH_s(f;p_i)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean#L862-L893

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FiniteEntropy.observableEntropy_mixture_joint_general {ι : Type uι} {α : Type uα} {β : Type uβ} [DecidableEq ι] [DecidableEq β]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) :
    observableEntropy (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => (ia.1,f ia.2)) =
      ∑ i ∈ t, ((∑ a ∈ s, p i a)*Real.negMulLog (w i)+
        w i*observableEntropy s (p i) f) := by sorry
