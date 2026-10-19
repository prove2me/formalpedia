-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_BallRatios_information_one_bound
-- name    : OAI.EntropyRateDimension.BallRatios.information_one_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:51:09.6495+00:00
-- url     : https://prove2.me/theorems/0f5d9d21-1a3a-457b-b892-1c4527f3f771
-- title:
--   Unit balls on a compact support have bounded information
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$ with compact support. Then there is $C\ge0$ such that every point $x$ of the support satisfies
--   $$
--   -\log\mu\bigl(\bar B(x,1)\bigr)\le C .
--   $$
--
--   So unit balls centred on the support have mass bounded away from zero.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/Clipping.lean#L32-L55

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.BallRatios
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
open scoped Topology BigOperators

theorem OAI.EntropyRateDimension.BallRatios.information_one_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hK : IsCompact μ.support) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ μ.support, information μ x 1 ≤ C := by sorry
