-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_LocalMass_dim_le_of_uniform_lower_mass
-- name    : OAI.EntropyRateDimension.LocalMass.dim_le_of_uniform_lower_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:39:45.950013+00:00
-- url     : https://prove2.me/theorems/dd3baa80-1d52-440c-8792-d0932c9eb389
-- title:
--   Uniform lower ball masses bound Hausdorff dimension
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$, $e\ge0$, $R>0$, and let $E\subseteq[-B,B]$ be a set such that
--   $$
--   \mu\bigl(B(x,r)\bigr)\ge(r/2)^e\qquad\text{for all }x\in E,\ 0<r<R .
--   $$
--   Then $\dim_HE\le e$.
--
--   This is the converse direction of the mass distribution principle, obtained by counting grid cells.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/MassDimension.lean#L13-L87

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
open MeasureEntropy

theorem OAI.EntropyRateDimension.LocalMass.dim_le_of_uniform_lower_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (E : Set ℝ) {B e R : ℝ} (he : 0 ≤ e) (hR : 0 < R)
    (hE : E ⊆ Icc (-B) B)
    (hball : ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < R →
      (r/2)^e ≤ μ.real (ball x r)) : dimH E ≤ ENNReal.ofReal e := by sorry
