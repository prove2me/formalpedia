-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_entropy_bound_of_radial_limit
-- name    : OAI.EntropyRateDimension.MeasureEntropy.entropy_bound_of_radial_limit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:39:08.760993+00:00
-- url     : https://prove2.me/theorems/d0347e99-8c6e-4d7d-84fe-fb6bd972bee4
-- title:
--   Averaged grid entropy grows at most like the local dimension
-- statement:
--   For a measure $\mu$ on $\mathbb R$ the local dimension at $x$ is the limit, when it exists, of $\log\mu(\bar B(x,r))/\log r$ as $r\to0^+$. The lower Hausdorff dimension $\underline{\dim}_H\mu$ is the infimum of $\dim_HE$ over measurable sets $E$ with $\mu(E)>0$.
--
--   Let $\mu$ be a compactly carried probability measure on $\mathbb R$ whose local dimension equals $d\ge0$ almost everywhere, and let $D>d$. Then there is $C$ with
--   $$
--   \bar H_s(\mu)\le D\log(1/s)+C\qquad(0<s<1),
--   $$
--   where $\bar H_s(\mu)$ is the grid entropy at mesh $s$ averaged over shifts.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/EntropyDimension.lean#L45-L89

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal

theorem OAI.EntropyRateDimension.MeasureEntropy.entropy_bound_of_radial_limit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : CompactlyCarried μ) {d D : ℝ} (hd : 0 ≤ d) (hD : d < D)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto
      (fun r => -Real.log (μ.real (Metric.closedBall x r)) / -Real.log r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d)) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s → s < 1 → averaged μ s ≤ D*Real.log (1/s)+C := by sorry
