-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_condition_le
-- name    : OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_condition_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:04:48.248784+00:00
-- url     : https://prove2.me/theorems/dc4bcae1-2433-4a23-b7cd-05d6db8f5d5f
-- title:
--   Conditioning on more information lowers conditional entropy
-- statement:
--   For a finite set $s$ and real weights $p$, the entropy is $H(s,p)=\sum_{a\in s}-p_a\log p_a$ in natural units. For an observable $f$, the mass of a value $b$ is $m_f(b)=\sum_{a\in s,\,f(a)=b}p_a$, the observable entropy $H(f)$ is the entropy of these masses over the image $f(s)$, and the conditional entropy is $H(f\mid g)=H(f,g)-H(g)$.
--
--   For nonnegative weights $p$ on $s$ and observables $f,g,h$,
--   $$
--   H\bigl(f\mid(h,g)\bigr)\le H(f\mid g) .
--   $$
--
--   Refining the conditioning observable can only decrease the conditional entropy.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean#L760-L777

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_condition_le {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ x ∈ s, 0 ≤ p x) :
    conditionalEntropy s p f (fun x => (h x,g x)) ≤ conditionalEntropy s p f g := by sorry
