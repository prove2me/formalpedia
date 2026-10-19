-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_DigitSumset_card_sumset_le
-- name    : OAI.EntropyRateDimension.DigitSumset.card_sumset_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:34:09.61384+00:00
-- url     : https://prove2.me/theorems/aa29c7c8-dbf8-4454-9376-87aee01b5fdb
-- title:
--   Sumsets of digit sets grow polynomially
-- statement:
--   Let $S$ be a finite set of reals each of the form $\sum_{j\in\beta}v_j(w_j)$ for a choice $w:\beta\to\alpha$ of digits, with $\alpha,\beta$ finite. Then the set of sums of $k$ elements of $S$ satisfies
--   $$
--   |kS|\le(k+1)^{|\beta|\,|\alpha|} .
--   $$
--
--   So the sumset grows at most polynomially in $k$, unlike the exponential growth of a generic set.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/DigitSumset.lean#L41-L59

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.DigitSumset
universe uα uβ
open scoped BigOperators

theorem OAI.EntropyRateDimension.DigitSumset.card_sumset_le {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β]
    (S : Finset ℝ) (v : β → α → ℝ)
    (hS : ∀ x ∈ S, ∃ w : β → α, x=∑ j, v j (w j)) (k : ℕ) :
    (sumset S k).card ≤ (k+1)^(Fintype.card β*Fintype.card α) := by sorry
