-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Windows_sum_disjoint_drops_le
-- name    : OAI.EntropyRateDimension.Windows.sum_disjoint_drops_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:33:30.482833+00:00
-- url     : https://prove2.me/theorems/603484cd-27ae-4f45-a6a7-7b9af32d95c3
-- title:
--   Drops of a nonnegative decreasing sequence over disjoint intervals
-- statement:
--   Let $g:\mathbb N\to\mathbb R$ be nonincreasing and nonnegative, and let $[u_i,v_i)$, for $i$ in a finite set $s$, be pairwise disjoint intervals with $u_i\le v_i$. Then
--   $$
--   \sum_{i\in s}\bigl(g(u_i)-g(v_i)\bigr)\le g(0) .
--   $$
--
--   The total decrease over disjoint stretches cannot exceed the total decrease from $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/Windows.lean#L45-L70

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound

open OAI OAI.EntropyRateDimension
universe uα
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.Windows.sum_disjoint_drops_le {α : Type uα} (s : Finset α) (u v : α → ℕ)
    (huv : ∀ i ∈ s, u i ≤ v i)
    (hd : (↑s : Set α).PairwiseDisjoint (fun i => Finset.Ico (u i) (v i)))
    (g : ℕ → ℝ) (hg : Antitone g) (hgn : ∀ i, 0 ≤ g i) :
    ∑ i ∈ s, (g (u i) - g (v i)) ≤ g 0 := by sorry
