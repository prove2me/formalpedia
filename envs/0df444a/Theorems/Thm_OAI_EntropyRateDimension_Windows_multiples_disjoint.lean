-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Windows_multiples_disjoint
-- name    : OAI.EntropyRateDimension.Windows.multiples_disjoint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:32:57.227694+00:00
-- url     : https://prove2.me/theorems/ad0166fd-afe8-4fc0-bf46-f0fe8452d42b
-- title:
--   Consecutive blocks of equal length are disjoint
-- statement:
--   For natural numbers $n$ and $j\ne k$, the blocks
--   $$
--   [jn,\ jn+n)\qquad\text{and}\qquad[kn,\ kn+n)
--   $$
--   are disjoint sets of natural numbers.
--
--   So the blocks of length $n$ starting at multiples of $n$ partition an initial segment.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/Windows.lean#L31-L43

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

theorem OAI.EntropyRateDimension.Windows.multiples_disjoint {n j k : ℕ} (hjk : j ≠ k) :
    Disjoint (Finset.Ico (j * n) (j * n + n)) (Finset.Ico (k * n) (k * n + n)) := by sorry
