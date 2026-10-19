-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_LocalMass_eventual_lower_of_limit
-- name    : OAI.EntropyRateDimension.LocalMass.eventual_lower_of_limit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:37:33.844392+00:00
-- url     : https://prove2.me/theorems/58562509-8fdd-4264-a05c-b5c066d5bd88
-- title:
--   A local dimension limit gives eventual lower mass bounds
-- statement:
--   Let $\mu$ be a finite measure on $\mathbb R$ and $x$ a point of its support, and suppose
--   $$
--   \lim_{r\to0^+}\frac{-\log\mu(\bar B(x,r))}{-\log r}=d .
--   $$
--   Then for every $e>d$ there is $R>0$ with $\mu(\bar B(x,r))\ge r^e$ for all $0<r<R$.
--
--   So the local dimension controls ball masses from below at all small scales.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/LocalMass.lean#L117-L136

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

theorem OAI.EntropyRateDimension.LocalMass.eventual_lower_of_limit (μ : Measure ℝ) [IsFiniteMeasure μ] {x e d : ℝ}
    (hx : x ∈ μ.support) (hde : d < e)
    (hlim : Tendsto (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r)
      (𝓝[>] 0) (𝓝 d)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r^e ≤ μ.real (closedBall x r) := by sorry
