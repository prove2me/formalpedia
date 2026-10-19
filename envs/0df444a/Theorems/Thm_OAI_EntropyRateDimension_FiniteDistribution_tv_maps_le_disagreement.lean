-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteDistribution_tv_maps_le_disagreement
-- name    : OAI.EntropyRateDimension.FiniteDistribution.tv_maps_le_disagreement
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:17:16.683196+00:00
-- url     : https://prove2.me/theorems/4f6322e6-9a8a-4419-8717-76804d19359f
-- title:
--   Total variation between two images of one distribution
-- statement:
--   Let $p$ be a finitely supported probability distribution on $\alpha$ and $f,g:\alpha\to\beta$ two maps. Then the total variation between the image distributions is at most the probability that the maps disagree:
--   $$
--   \mathrm{TV}(f_*p,g_*p)\le\sum_{a\in\mathrm{supp}\,p,\ f(a)\ne g(a)}p(a),
--   $$
--   where $\mathrm{TV}(p,q)=\frac12\sum_b|p(b)-q(b)|$.
--
--   In coupling language: the two images are coupled through the same point $a$, so they differ only where the maps do.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/RandomGrid.lean#L35-L81

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteDistribution
universe uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem OAI.EntropyRateDimension.FiniteDistribution.tv_maps_le_disagreement {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f g : α → β) :
    (p.map f).tv (p.map g) ≤ ∑ a ∈ p.support, if f a = g a then 0 else p.weight a := by sorry
