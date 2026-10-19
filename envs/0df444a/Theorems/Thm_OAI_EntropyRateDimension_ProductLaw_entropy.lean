-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_ProductLaw_entropy
-- name    : OAI.EntropyRateDimension.ProductLaw.entropy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:24:33.68399+00:00
-- url     : https://prove2.me/theorems/ab16cf83-daa5-4572-aac7-41c277392f78
-- title:
--   Entropy of a product law is the sum of entropies
-- statement:
--   Let $p_i$ be probability weights on a finite set $A$ for each $i$ in a finite index set, and $p(x)=\prod_ip_i(x_i)$ the product weight. Then
--   $$
--   H(p)=\sum_iH(p_i),\qquad H(q)=\sum_a-q(a)\log q(a).
--   $$
--
--   Entropy is additive over independent coordinates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/ProductLaw.lean#L64-L83

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

theorem OAI.EntropyRateDimension.ProductLaw.entropy (p : ι → α → ℝ) (hp : ∀ i, ∑ a, p i a = 1) :
    FiniteEntropy.entropy Finset.univ (weight p) =
      ∑ i, FiniteEntropy.entropy Finset.univ (p i) := by sorry
