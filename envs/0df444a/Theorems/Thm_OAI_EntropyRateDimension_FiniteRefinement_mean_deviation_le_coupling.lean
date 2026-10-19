-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteRefinement_mean_deviation_le_coupling
-- name    : OAI.EntropyRateDimension.FiniteRefinement.mean_deviation_le_coupling
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:29:01.872799+00:00
-- url     : https://prove2.me/theorems/24716b96-52e5-4326-a624-1d3e59726436
-- title:
--   Mean deviation from cell means is bounded by a within-cell coupling
-- statement:
--   Let $p>0$ be weights on a finite set, $v$ a real function and $g$ a partition label, with cell masses $m(c)=\sum_{g(b)=c}p(b)$ and cell means $\bar v(c)=\sum_{g(b)=c}\frac{p(b)}{m(c)}v(b)$. Then
--   $$
--   \sum_ap(a)\,|v(a)-\bar v(g(a))|\le\sum_{a,b:\ g(a)=g(b)}\frac{p(a)p(b)}{m(g(a))}\,|v(a)-v(b)| .
--   $$
--
--   The right side is the transport cost of the coupling that pairs points of the same cell independently.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteRefinement.lean#L167-L201

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteRefinement
universe uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory
open FiniteEntropy
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem OAI.EntropyRateDimension.FiniteRefinement.mean_deviation_le_coupling (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 < p a) :
    (∑ a, p a * |v a-cellMean p v g (g a)|) ≤
      ∑ a, ∑ b, (if g a = g b then p a*p b/mass Finset.univ p g (g a) else 0) *
        |v a-v b| := by sorry
