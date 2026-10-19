-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_le_bad_mass
-- name    : OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_le_bad_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:00:33.267977+00:00
-- url     : https://prove2.me/theorems/1ac0cf82-14ab-409b-82ca-e4ac18b06737
-- title:
--   Conditional entropy is controlled by the mass of bad fibres
-- statement:
--   For a finite set $s$ and real weights $p$, the entropy is $H(s,p)=\sum_{a\in s}-p_a\log p_a$ in natural units. For an observable $f$, the mass of a value $b$ is $m_f(b)=\sum_{a\in s,\,f(a)=b}p_a$, the observable entropy $H(f)$ is the entropy of these masses over the image $f(s)$, and the conditional entropy is $H(f\mid g)=H(f,g)-H(g)$.
--
--   Let $p\ge0$ on $s$, let $f,g$ be observables, and let $\mathrm{bad}$ be a predicate on values of $g$. Suppose $f$ is constant on each fibre of $g$ whose value is not bad. Then
--   $$
--   H(f\mid g)\le\Bigl(\sum_{a\in s,\ \mathrm{bad}(g(a))}p_a\Bigr)\log|f(s)| .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean#L419-L461

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_le_bad_mass {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (bad : γ → Prop) [DecidablePred bad] (hp : ∀ a ∈ s, 0 ≤ p a)
    (hgood : ∀ a ∈ s, ∀ b ∈ s, g a = g b → ¬bad (g a) → f a = f b) :
    conditionalEntropy s p f g ≤
      (∑ a ∈ s, if bad (g a) then p a else 0) * Real.log (s.image f).card := by sorry
