-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_good_labels_card_bound
-- name    : OAI.EntropyRateDimension.MeasureEntropy.good_labels_card_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:34:56.018136+00:00
-- url     : https://prove2.me/theorems/b58df219-9ec5-4b1a-8520-62cd163f8f7e
-- title:
--   Few grid cells can contain heavy balls
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$ and $s>0$. Let $a$ be a finite set of grid labels, and for each $i\in a$ let $x_i$ be a point with $\lfloor x_i/s+u\rfloor=i$ and $\mu\bigl(B(x_i,s/2)\bigr)\ge q$. Then
--   $$
--   |a|\cdot q\le3 .
--   $$
--
--   Each heavy ball meets few others, so at most $3/q$ cells contain the centre of a ball of mass $q$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/LocalEntropy.lean#L148-L176

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.MeasureEntropy.good_labels_card_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s u q : ℝ} (hs : 0 < s) (a : Finset ℤ) (x : ℤ → ℝ)
    (hx : ∀ i ∈ a, label s u (x i)=i)
    (hq : ∀ i ∈ a, q ≤ μ.real (Metric.ball (x i) (s/2))) :
    (a.card : ℝ)*q ≤ 3 := by sorry
