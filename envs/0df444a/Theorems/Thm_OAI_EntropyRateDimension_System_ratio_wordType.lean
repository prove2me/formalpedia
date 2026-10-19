-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_System_ratio_wordType
-- name    : OAI.EntropyRateDimension.System.ratio_wordType
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:08:00.580997+00:00
-- url     : https://prove2.me/theorems/0e617d9d-4797-44b6-ac7d-7cd33fdb15cd
-- title:
--   Blocks of the same type have the same ratio
-- statement:
--   Let $S$ be a system with ratios $r_i$, and $b\ge1$. The type of a block $w$ of length $b$ is its vector of letter counts $(\#\{j:w_j=i\})_i$. If two blocks $w,v$ have the same type, then their ratios in the block system agree:
--   $$
--   \prod_{j<b}r_{w_j}=\prod_{j<b}r_{v_j} .
--   $$
--
--   So the word type can serve as a tag that determines the contraction ratio.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/BlockWords.lean#L119-L134

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
universe uι uα uβ uγ
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

theorem OAI.EntropyRateDimension.System.ratio_wordType (S : System ι) {b : ℕ} (hb : 0 < b) (w v : Fin b → ι)
    (h : wordType w=wordType v) : (S.blocks hb).ratio w=(S.blocks hb).ratio v := by sorry
