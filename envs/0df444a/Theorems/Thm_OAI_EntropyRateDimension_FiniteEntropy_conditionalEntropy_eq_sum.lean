-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_eq_sum
-- name    : OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_eq_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T03:59:54.011314+00:00
-- url     : https://prove2.me/theorems/f4e6ad3f-18dd-4f17-aac9-b569a00ad8f5
-- title:
--   Conditional entropy as an average over fibres
-- statement:
--   For a finite set $s$ and real weights $p$, the entropy is $H(s,p)=\sum_{a\in s}-p_a\log p_a$ in natural units. For an observable $f$, the mass of a value $b$ is $m_f(b)=\sum_{a\in s,\,f(a)=b}p_a$, the observable entropy $H(f)$ is the entropy of these masses over the image $f(s)$, and the conditional entropy is $H(f\mid g)=H(f,g)-H(g)$.
--
--   For nonnegative weights $p$ on $s$ and observables $f,g$,
--   $$
--   H(f\mid g)=\sum_{c\in g(s)}m_g(c)\;H_{s_c}\Bigl(f;\ \frac{p}{m_g(c)}\Bigr),
--   $$
--   where $s_c=\{a\in s:g(a)=c\}$ and $H_{s_c}(f;q)$ is the observable entropy of $f$ on $s_c$ under the weights $q$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean#L342-L373

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_eq_sum {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    conditionalEntropy s p f g = ∑ c ∈ s.image g, mass s p g c *
      observableEntropy (s.filter (fun a => g a = c)) (fun a => p a / mass s p g c) f := by sorry
