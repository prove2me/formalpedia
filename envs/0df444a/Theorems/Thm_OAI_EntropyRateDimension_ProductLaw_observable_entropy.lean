-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_ProductLaw_observable_entropy
-- name    : OAI.EntropyRateDimension.ProductLaw.observable_entropy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:25:00.084691+00:00
-- url     : https://prove2.me/theorems/1ca0be46-92ed-4511-ad68-183a37382696
-- title:
--   Entropy of a coordinatewise observable of an i.i.d. law
-- statement:
--   Let $p$ be probability weights on a finite nonempty set $A$, $g:A\to\beta$ an observable, and $I$ a finite index set. Under the i.i.d. product weights $\prod_{i\in I}p(x_i)$ on $A^I$, the observable $x\mapsto(g(x_i))_{i\in I}$ has entropy
--   $$
--   H\bigl((g(x_i))_i\bigr)=|I|\cdot H_p(g),
--   $$
--   where $H_p(g)$ is the entropy of the law of $g$ under $p$.
--
--   Entropy is additive over the independent coordinates, also after applying the same observable to each.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/ProductLaw.lean#L153-L194

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.ProductLaw
universe uι uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory
variable {ι : Type uι} {α : Type uα} [Fintype ι] [DecidableEq ι] [Fintype α]
variable {β : Type uβ} [DecidableEq β]

theorem OAI.EntropyRateDimension.ProductLaw.observable_entropy [Nonempty α] [Nonempty β]
    (p : α → ℝ) (g : α → β) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    FiniteEntropy.observableEntropy Finset.univ (weight (fun _ : ι => p)) (fun x i => g (x i)) =
      Fintype.card ι * FiniteEntropy.observableEntropy Finset.univ p g := by sorry
