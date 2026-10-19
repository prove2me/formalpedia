-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_grid_support_card_le
-- name    : OAI.EntropyRateDimension.MeasureEntropy.grid_support_card_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:36:59.898596+00:00
-- url     : https://prove2.me/theorems/0bfe68e9-d6be-466a-b21d-0bec3e6c946b
-- title:
--   Number of grid cells meeting a bounded interval
-- statement:
--   Let $B\ge0$ and $0<s\le1$. The number of integers in the range $\bigl[\lfloor-B/s\rfloor,\ \lfloor B/s+1\rfloor\bigr]$, which contains every grid label $\lfloor x/s+u\rfloor$ of a point $x\in[-B,B]$ with $u\in[0,1]$, is at most
--   $$
--   \frac{2B+3}s .
--   $$
--
--   This bounds the entropy of a grid label by $\log((2B+3)/s)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/LocalEntropy.lean#L211-L227

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

theorem OAI.EntropyRateDimension.MeasureEntropy.grid_support_card_le {B s : ℝ} (hB : 0 ≤ B) (hs : 0 < s) (hs1 : s ≤ 1) :
    ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ) ≤ (2*B+3)/s := by sorry
