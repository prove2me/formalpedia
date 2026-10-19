-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_LocalMass_large_uniform_mass_set
-- name    : OAI.EntropyRateDimension.LocalMass.large_uniform_mass_set
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:38:36.577994+00:00
-- url     : https://prove2.me/theorems/e90e8613-da9a-45d7-8acd-0f5d5be36272
-- title:
--   Uniform lower mass bounds on a large set
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$, $e\ge0$ and $\eta>0$. Suppose that at almost every $x$ there is $R_x>0$ with $\mu(\bar B(x,r))\ge r^e$ for $0<r<R_x$. Then there are a measurable set $E$ with $\mu(E^c)\le\eta$ and a single radius $R>0$ such that
--   $$
--   \mu\bigl(B(x,r)\bigr)\ge(r/2)^e\qquad\text{for all }x\in E,\ 0<r<R .
--   $$
--
--   So pointwise bounds become uniform on a set of almost full measure, at the cost of halving the radius.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/LocalMass.lean#L161-L206

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

theorem OAI.EntropyRateDimension.LocalMass.large_uniform_mass_set (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e η : ℝ} (he : 0 ≤ e) (hη : 0 < η)
    (hlocal : ∀ᵐ x ∂μ, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r^e ≤ μ.real (closedBall x r)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ μ.real Eᶜ ≤ η ∧
      ∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < R →
        (r/2)^e ≤ μ.real (ball x r) := by sorry
