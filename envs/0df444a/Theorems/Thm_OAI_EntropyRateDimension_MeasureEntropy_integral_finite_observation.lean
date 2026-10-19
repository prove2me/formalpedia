-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_integral_finite_observation
-- name    : OAI.EntropyRateDimension.MeasureEntropy.integral_finite_observation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:19:08.902213+00:00
-- url     : https://prove2.me/theorems/b2a3bf31-4bb4-4a72-bcac-4d98ac9a91f7
-- title:
--   Integrals of a finitely valued observable
-- statement:
--   Let $\mu$ be a finite measure, $f$ a measurable observable with values in a type with measurable singletons, and suppose $f$ lies in a finite set $s$ almost everywhere. Then for every real function $F$,
--   $$
--   \int F(f(x))\,d\mu(x)=\sum_{b\in s}\mu\{f=b\}\,F(b) .
--   $$
--
--   This is the expectation formula for a discrete random variable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/RandomGrid.lean#L144-L161

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.MeasureEntropy.integral_finite_observation {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s)
    (F : β → ℝ) : ∫ x, F (f x) ∂μ = ∑ b ∈ s, mass μ f b*F b := by sorry
