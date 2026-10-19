-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FairPairs_geometric_fine_scale_bound
-- name    : OAI.EntropyRateDimension.FairPairs.geometric_fine_scale_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:22:24.954093+00:00
-- url     : https://prove2.me/theorems/9fa525f2-360b-4800-aafb-748a436ceae7
-- title:
--   A geometric sum with bounded terms is bounded
-- statement:
--   Let $s$ be a finite set of natural numbers and $a\ge0$, and suppose every term satisfies $a\,4^h\le2$ for $h\in s$. Then
--   $$
--   \sum_{h\in s}a\,4^h\le\frac83 .
--   $$
--
--   The bound holds because the largest term dominates a geometric series of ratio $\frac14$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FairPairs.lean#L390-L410

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FairPairs
universe uι uα uβ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FairPairs.geometric_fine_scale_bound (s : Finset ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hs : ∀ h ∈ s, a * (4 : ℝ)^h ≤ 2) :
    (∑ h ∈ s, a * (4 : ℝ)^h) ≤ 8 / 3 := by sorry
