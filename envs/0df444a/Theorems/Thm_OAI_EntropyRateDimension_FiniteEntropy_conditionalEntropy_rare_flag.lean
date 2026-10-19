-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_rare_flag
-- name    : OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_rare_flag
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:01:13.729558+00:00
-- url     : https://prove2.me/theorems/490797d1-5023-47f1-81c8-9687b77a8200
-- title:
--   Conditional entropy given a rare flag
-- statement:
--   For a finite set $s$ and real weights $p$, the entropy is $H(s,p)=\sum_{a\in s}-p_a\log p_a$ in natural units. For an observable $f$, the mass of a value $b$ is $m_f(b)=\sum_{a\in s,\,f(a)=b}p_a$, the observable entropy $H(f)$ is the entropy of these masses over the image $f(s)$, and the conditional entropy is $H(f\mid g)=H(f,g)-H(g)$.
--
--   Let $p$ be a probability on $s$, let $C,Y$ be observables, let $E$ be a Boolean flag and $B$ a predicate on values of $Y$. Suppose $C=c_0$ whenever $E$ is false and $B(Y)$ fails. Writing $q=m_E(\mathrm{true})$,
--   $$
--   H(C\mid Y)\le h(q)+\Bigl(q+\sum_{a:\,B(Y(a))}p_a\Bigr)\log|C(s)|,
--   $$
--   where $h$ is the binary entropy in natural units.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean#L474-L511

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_rare_flag {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (C : α → β) (Y : α → γ) (E : α → Bool)
    (B : γ → Prop) [DecidablePred B] (c₀ : β)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1)
    (hgood : ∀ a ∈ s, E a = false → ¬B (Y a) → C a = c₀) :
    conditionalEntropy s p C Y ≤ Real.binEntropy (mass s p E true) +
      (mass s p E true + ∑ a ∈ s.filter (fun a => B (Y a)), p a) *
        Real.log (s.image C).card := by sorry
