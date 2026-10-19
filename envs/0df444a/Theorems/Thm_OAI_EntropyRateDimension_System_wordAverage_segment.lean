-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_System_wordAverage_segment
-- name    : OAI.EntropyRateDimension.System.wordAverage_segment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:59:37.23078+00:00
-- url     : https://prove2.me/theorems/0c97646a-9876-45e3-80e3-46b1fc6831ea
-- title:
--   Averages over a segment of a random word
-- statement:
--   Let $\mathbb E_H[F]=\sum_{|W|=H}w(W)F(W)$ be the average of a function of words over random words of length $H$ with independent letters distributed by the weights $w_i$. If $j+n\le H$, then for every function $f$ of lists,
--   $$
--   \mathbb E_H\bigl[f(W_{[j,j+n)})\bigr]=\mathbb E_n[f],
--   $$
--   where $W_{[j,j+n)}$ is the segment of $n$ letters starting at position $j$.
--
--   So segments of random words are again random words.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/WordAverage.lean#L48-L65

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
universe uι uα
open scoped BigOperators
variable {α : Type uα} [Fintype α]

theorem OAI.EntropyRateDimension.System.wordAverage_segment (S : System α) {H j n : ℕ} (hH : j+n ≤ H) (f : List α → ℝ) :
    S.wordAverage H (fun W => f ((W.drop j).take n))=S.wordAverage n f := by sorry
