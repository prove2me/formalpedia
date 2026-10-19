-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_ProductLaw_moment
-- name    : OAI.EntropyRateDimension.ProductLaw.moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:22:56.771584+00:00
-- url     : https://prove2.me/theorems/9da8aa64-9c34-4156-a79c-383125101fc2
-- title:
--   Moments of products under product weights
-- statement:
--   Let $p_i$ be probability weights on a finite set $A$ for each $i$ in a finite index set, and let $p(x)=\prod_ip_i(x_i)$ be the product weight on $A^I$. For functions $f_i$ on $A$ and a subset $s\subseteq I$,
--   $$
--   \sum_xp(x)\prod_{i\in s}f_i(x_i)=\prod_{i\in s}\sum_ap_i(a)f_i(a) .
--   $$
--
--   So coordinates are independent under product weights.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/ProductLaw.lean#L25-L39

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

theorem OAI.EntropyRateDimension.ProductLaw.moment (p f : ι → α → ℝ) (s : Finset ι)
    (hp : ∀ i, ∑ a, p i a = 1) :
    (∑ x, weight p x * ∏ i ∈ s, f i (x i)) = ∏ i ∈ s, ∑ a, p i a * f i a := by sorry
