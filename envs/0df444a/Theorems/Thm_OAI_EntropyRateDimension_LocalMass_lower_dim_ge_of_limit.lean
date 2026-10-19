-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_LocalMass_lower_dim_ge_of_limit
-- name    : OAI.EntropyRateDimension.LocalMass.lower_dim_ge_of_limit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:38:06.382165+00:00
-- url     : https://prove2.me/theorems/d333da69-c199-45ef-99bf-f9f9d9a08282
-- title:
--   Lower Hausdorff dimension is at least the almost sure local dimension
-- statement:
--   For a measure $\mu$ on $\mathbb R$ the local dimension at $x$ is the limit, when it exists, of $\log\mu(\bar B(x,r))/\log r$ as $r\to0^+$. The lower Hausdorff dimension $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over measurable sets $E$ with $\mu(E)>0$.
--
--   Let $\mu$ be a probability measure on $\mathbb R$ whose local dimension exists and equals $d$ at $\mu$-almost every point. Then
--   $$
--   \underline{\dim}_H\mu\ge d .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/LocalMass.lean#L138-L159

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

open OAI OAI.EntropyRateDimension
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal

theorem OAI.EntropyRateDimension.LocalMass.lower_dim_ge_of_limit (μ : Measure ℝ) [IsProbabilityMeasure μ] {d : ℝ}
    (hlim : ∀ᵐ x ∂μ, Tendsto
      (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r) (𝓝[>] 0) (𝓝 d)) :
    ENNReal.ofReal d ≤ lowerHausdorffDimension μ := by sorry
