-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_mixture
-- name    : OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_mixture
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:06:28.98099+00:00
-- url     : https://prove2.me/theorems/c4d2f1b5-a3e6-4891-815d-534312bb05e7
-- title:
--   Conditional entropy is concave in the distribution
-- statement:
--   For a finite set $s$ and real weights $p$, the entropy is $H(s,p)=\sum_{a\in s}-p_a\log p_a$ in natural units. For an observable $f$, the mass of a value $b$ is $m_f(b)=\sum_{a\in s,\,f(a)=b}p_a$, the observable entropy $H(f)$ is the entropy of these masses over the image $f(s)$, and the conditional entropy is $H(f\mid g)=H(f,g)-H(g)$.
--
--   Let $w_i\ge0$ for $i\in t$, and let $p_i$ be probability weights on $s$. For observables $f,g$,
--   $$
--   \sum_{i\in t}w_i\,H_{p_i}(f\mid g)\le H_{\bar p}(f\mid g),\qquad\bar p=\sum_{i\in t}w_ip_i .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean#L832-L860

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_mixture {ι : Type uι} {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq ι] [DecidableEq β] [DecidableEq γ]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) (g : α → γ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hp : ∀ i ∈ t, ∀ a ∈ s, 0 ≤ p i a)
    (hp1 : ∀ i ∈ t, ∑ a ∈ s, p i a = 1) :
    (∑ i ∈ t, w i*conditionalEntropy s (p i) f g) ≤
      conditionalEntropy s (fun a => ∑ i ∈ t, w i*p i a) f g := by sorry
