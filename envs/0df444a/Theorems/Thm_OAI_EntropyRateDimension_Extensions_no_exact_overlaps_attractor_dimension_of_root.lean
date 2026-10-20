-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Extensions_no_exact_overlaps_attractor_dimension_of_root
-- name    : OAI.EntropyRateDimension.Extensions.no_exact_overlaps_attractor_dimension_of_root
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:28:12.42593+00:00
-- url     : https://prove2.me/theorems/574543c7-41d0-40fb-98df-4687156f1d98
-- title:
--   Hausdorff dimension of attractors without exact overlaps
-- statement:
--   A self-similar system on the line consists of finitely many maps $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$; a probability measure $\mu$ is self-similar when $\mu=\sum_iw_i(f_i)_*\mu$. The coding map sends an address $\omega\in\iota^{\mathbb N}$ to $\pi(\omega)=\lim_nf_{\omega_0}\circ\cdots\circ f_{\omega_{n-1}}(0)$, and the system has no exact overlaps when distinct finite words give distinct composed maps. Let $K$ be the attractor. If the system has no exact overlaps, $s\ge0$ and $\sum_i|r_i|^s=1$, then
--   $$
--   \dim_HK=\min(1,s).
--   $$
--
--   So without exact overlaps the attractor of a family of similarities on the line has the expected dimension.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/AttractorDimension.lean#L126-L141

import Mathlib
import Definitions.Def_SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Model
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RetainedLoss__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairBands__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowCount__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowGain__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Main__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_NoOverlaps
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Attractor
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_AttractorDimension

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Extensions
universe uι
open scoped BigOperators ENNReal Topology
open MeasureTheory Set Filter
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

theorem OAI.EntropyRateDimension.Extensions.no_exact_overlaps_attractor_dimension_of_root (S : System ι) {s : ℝ}
    (hs : 0 ≤ s) (hroot : ∑ i, |S.ratio i| ^ s = 1) (h : NoExactOverlaps S) :
    dimH (attractor S) = ENNReal.ofReal (min 1 s) := by sorry
