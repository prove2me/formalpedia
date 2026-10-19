-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Coding_head_point_law
-- name    : OAI.EntropyRateDimension.Coding.head_point_law
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:49:14.178401+00:00
-- url     : https://prove2.me/theorems/97412466-5afd-4462-aa9e-1274c25aecc5
-- title:
--   Joint law of the first letter and the coded point
-- statement:
--   Let $f_i(x)=r_ix+b_i$ be a finite system with weights $w_i>0$ summing to $1$, let $P$ be the Bernoulli measure on sequences $\omega$ with marginal $\sum_iw_i\delta_i$, let $\pi(\omega)=\sum_n\bigl(\prod_{j<n}r_{\omega_j}\bigr)b_{\omega_n}$ be the coding map, and let $\mu=\pi_*P$ be the self-similar law. Write $\mathrm{slope}_n(\omega)=\prod_{j<n}r_{\omega_j}$ and $I(x,r)=-\log\mu(\bar B(x,r))$.
--
--   Then the joint law of the first letter and the coded point is
--   $$
--   \bigl(\omega\mapsto(\omega_0,\pi(\omega))\bigr)_*P=\sum_i\delta_i\otimes w_i(f_i)_*\mu .
--   $$
--   So, given that the first letter is $i$, the coded point is distributed as the $i$-th component of $\mu$, normalized.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/CodingIntegrals.lean#L27-L53

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
open MeasureTheory Metric Set Filter EntropyRateDimension.Bernoulli
open scoped Topology BigOperators ENNReal
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

theorem OAI.EntropyRateDimension.Coding.head_point_law (S : System ι) :
    (addressMeasure S).map (fun ω => (ω 0,point S ω)) =
      ∑ i, (Measure.dirac i).prod (S.component (law S) i) := by sorry
