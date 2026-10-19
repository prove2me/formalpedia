-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_entropy_binary_extra
-- name    : OAI.EntropyRateDimension.MeasureEntropy.entropy_binary_extra
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:19:47.677481+00:00
-- url     : https://prove2.me/theorems/058393b3-39a0-4713-a8d6-2f61ad768b9c
-- title:
--   A binary label that is rarely nonzero adds little entropy
-- statement:
--   Let $\mu$ be a probability measure, $f$ a measurable observable lying in a finite set almost surely, and $g$ an integer observable with values in $\{0,1\}$ almost surely. Let $\mathrm{bad}$ be a predicate on values of $f$, and suppose $g=0$ almost surely wherever $f$ is not bad. Then
--   $$
--   H(g,f)-H(f)\le\mu\{\mathrm{bad}(f)\}\,\log2 .
--   $$
--
--   Here $H$ denotes the entropy of the law of an observable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/RandomGrid.lean#L163-L215

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

theorem OAI.EntropyRateDimension.MeasureEntropy.entropy_binary_extra {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq β]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β) (g : α → ℤ)
    (hf : Measurable f) (hg : Measurable g) (s : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (hg01 : ∀ᵐ x ∂μ, g x ∈ Finset.Icc (0 : ℤ) 1)
    (bad : β → Prop) [DecidablePred bad]
    (hgood : ∀ᵐ x ∂μ, ¬bad (f x) → g x=0) :
    entropy μ (fun x => (g x,f x))-entropy μ f ≤
      (∫ x, if bad (f x) then (1 : ℝ) else 0 ∂μ)*Real.log 2 := by sorry
