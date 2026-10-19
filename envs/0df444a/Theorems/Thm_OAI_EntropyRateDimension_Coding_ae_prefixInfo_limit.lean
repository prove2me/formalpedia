-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Coding_ae_prefixInfo_limit
-- name    : OAI.EntropyRateDimension.Coding.ae_prefixInfo_limit
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-19T04:51:39.771265+00:00
-- url     : https://prove2.me/theorems/cdd1fff4-9bed-4e97-b6de-f4f4cee4951f
-- title:
--   Information of shrinking balls grows linearly along the coding
-- statement:
--   Let $f_i(x)=r_ix+b_i$ be a finite system with weights $w_i>0$ summing to $1$, let $P$ be the Bernoulli measure on sequences $\omega$ with marginal $\sum_iw_i\delta_i$, let $\pi(\omega)=\sum_n\bigl(\prod_{j<n}r_{\omega_j}\bigr)b_{\omega_n}$ be the coding map, and let $\mu=\pi_*P$ be the self-similar law. Write $\mathrm{slope}_n(\omega)=\prod_{j<n}r_{\omega_j}$ and $I(x,r)=-\log\mu(\bar B(x,r))$.
--
--   Let $\mathrm{IR}=\int-\log w_{\omega_0}\,dP-\int\kappa\,dP$, where $\kappa(\omega)$ is the limiting log ratio of $\mu$ to its $\omega_0$-th component at the coded point. Then for $P$-almost every $\omega$,
--   $$
--   \lim_{n\to\infty}\frac1n\,I\bigl(\pi(\omega),|\mathrm{slope}_n(\omega)|\bigr)=\mathrm{IR}.
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/BallLimits.lean#L158-L177

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Coding
universe uι
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Metric Set Filter
open EntropyRateDimension.Bernoulli EntropyRateDimension.ErgodicAux
open scoped Topology BigOperators
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_1
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_1
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

theorem OAI.EntropyRateDimension.Coding.ae_prefixInfo_limit (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => prefixInfo S n ω / (n : ℝ)) atTop (𝓝 (infoRate S)) := by sorry
