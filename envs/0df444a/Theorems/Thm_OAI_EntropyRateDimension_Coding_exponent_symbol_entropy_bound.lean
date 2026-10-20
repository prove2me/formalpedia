-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Coding_exponent_symbol_entropy_bound
-- name    : OAI.EntropyRateDimension.Coding.exponent_symbol_entropy_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:14:01.696254+00:00
-- url     : https://prove2.me/theorems/c7455344-08a2-4aca-96c4-cb07a941ef12
-- title:
--   The coding exponent is bounded by symbol entropy over Lyapunov exponent
-- statement:
--   A self-similar system on the line consists of finitely many maps $f_i(x)=r_ix+b_i$ with $0<|r_i|<1$ and weights $w_i>0$ summing to $1$; a probability measure $\mu$ is self-similar when $\mu=\sum_iw_i(f_i)_*\mu$. The coding map sends an address $\omega\in\iota^{\mathbb N}$ to $\pi(\omega)=\lim_nf_{\omega_0}\circ\cdots\circ f_{\omega_{n-1}}(0)$, and the system has no exact overlaps when distinct finite words give distinct composed maps. Let $\alpha$ be the coding exponent, the almost-sure local dimension of the self-similar measure, and $\chi=-\sum_iw_i\log_2|r_i|$. Then
--   $$
--   \alpha\,\chi\,\log2\le-\sum_iw_i\log w_i .
--   $$
--
--   This is the upper bound $\alpha\le h_{\mathrm{sym}}/\chi_{\mathrm{nat}}$ in the dimension formula, valid with or without overlaps.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/UpperBound.lean#L167-L183

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Coding
universe uι uM
open MeasureTheory
open scoped BigOperators
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_5
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_5
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

theorem OAI.EntropyRateDimension.Coding.exponent_symbol_entropy_bound (S : System ι) :
    exponent S * S.lyapunov * Real.log 2 ≤ ∑ i, Real.negMulLog (S.weight i) := by sorry
