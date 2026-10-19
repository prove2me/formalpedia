-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_mass_comp
-- name    : OAI.EntropyRateDimension.MeasureEntropy.mass_comp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:08:50.070992+00:00
-- url     : https://prove2.me/theorems/8f11c4dc-5117-4346-9b4e-ba0a37216ae9
-- title:
--   Masses of a composed observable
-- statement:
--   Let $\mu$ be a finite measure, $f$ a measurable observable with values in a type with measurable singletons, and suppose $f$ takes values in a finite set $s$ almost everywhere. For any $g$ and value $c$,
--   $$
--   \mu\{g\circ f=c\}=\sum_{b\in s,\ g(b)=c}\mu\{f=b\} .
--   $$
--
--   So the law of $g\circ f$ is the image under $g$ of the finite law of $f$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean#L158-L183

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.MeasureEntropy.mass_comp {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) (c : γ) :
    mass μ (g ∘ f) c = FiniteEntropy.mass s (mass μ f) g c := by sorry
