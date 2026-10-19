-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_System_selfSimilar_words
-- name    : OAI.EntropyRateDimension.System.selfSimilar_words
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:54:53.547477+00:00
-- url     : https://prove2.me/theorems/887f978e-c572-4821-9ccf-9ec2942181db
-- title:
--   Self-similarity over words of length n
-- statement:
--   Let $\mu=\sum_iw_i(f_i)_*\mu$ be a self-similar measure for affine maps $f_i$ with weights $w_i$. For each $n$,
--   $$
--   \mu=\sum_{|w|=n}\Bigl(\prod_{j<n}w_{w_j}\Bigr)\,(f_{w_0}\circ\cdots\circ f_{w_{n-1}})_*\mu ,
--   $$
--   the sum running over all words $w$ of length $n$.
--
--   So $\mu$ is also self-similar for the system of composed maps of length $n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/UpperBound.lean#L40-L63

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
universe uι uM
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

theorem OAI.EntropyRateDimension.System.selfSimilar_words (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ) (n : ℕ) :
    μ = ∑ w : Fin n → ι, ENNReal.ofReal (S.wordWeight w) • μ.map (S.wordMap w) := by sorry
