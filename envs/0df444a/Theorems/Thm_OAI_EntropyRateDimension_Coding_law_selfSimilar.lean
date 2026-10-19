-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_Coding_law_selfSimilar
-- name    : OAI.EntropyRateDimension.Coding.law_selfSimilar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:40:52.910466+00:00
-- url     : https://prove2.me/theorems/f79762c7-c0f5-4b16-846a-c0efdf34af5a
-- title:
--   The coding law is self-similar
-- statement:
--   Let $f_i(x)=r_ix+b_i$ be a finite system with weights $w_i$. Let $\pi(\omega)=\sum_n\bigl(\prod_{j<n}r_{\omega_j}\bigr)b_{\omega_n}$ be the coding map, and $\mu=\pi_*P$ the image of the Bernoulli measure $P$ with marginal $\sum_iw_i\delta_i$. Then
--   $$
--   \mu=\sum_iw_i\,(f_i)_*\mu .
--   $$
--
--   So the law of the coding is a self-similar measure of the system.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/Coding.lean#L129-L152

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Coding
universe uι
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open Filter Set
open scoped Topology
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem OAI.EntropyRateDimension.Coding.law_selfSimilar (S : System ι) : S.SelfSimilar (law S) := by sorry
