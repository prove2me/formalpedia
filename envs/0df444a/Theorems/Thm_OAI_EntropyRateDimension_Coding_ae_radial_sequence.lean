-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Coding_ae_radial_sequence
-- name    : OAI.EntropyRateDimension.Coding.ae_radial_sequence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:53:07.523856+00:00
-- url     : https://prove2.me/theorems/dbe1f680-4d82-4f39-a39e-c14e22e32962
-- title:
--   Local dimension along exponential radii
-- statement:
--   Let $f_i(x)=r_ix+b_i$ be a finite system with weights $w_i>0$ summing to $1$, let $P$ be the Bernoulli measure on sequences $\omega$ with marginal $\sum_iw_i\delta_i$, let $\pi(\omega)=\sum_n\bigl(\prod_{j<n}r_{\omega_j}\bigr)b_{\omega_n}$ be the coding map, and let $\mu=\pi_*P$ be the self-similar law. Write $\mathrm{slope}_n(\omega)=\prod_{j<n}r_{\omega_j}$ and $I(x,r)=-\log\mu(\bar B(x,r))$.
--
--   Let $\alpha=\mathrm{IR}/(\chi\log2)$ be the coding exponent, where $\chi=-\sum_iw_i\log_2|r_i|$. Then for $\mu$-almost every $x$,
--   $$
--   \lim_{n\to\infty}\frac{-\log\mu\bigl(\bar B(x,e^{-n})\bigr)}n=\alpha .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/RadialLimit.lean#L73-L88

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
open Set Filter
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_3
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_3
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

theorem OAI.EntropyRateDimension.Coding.ae_radial_sequence (S : System ι) : ∀ᵐ x ∂law S,
    Tendsto (fun n : ℕ => BallRatios.information (law S) x (Real.exp (-(n : ℝ))) / (n : ℝ))
      atTop (𝓝 (exponent S)) := by sorry
