-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_integral_prod_mul_of_split
-- name    : GlobalTheory.FunObj.integral_prod_mul_of_split
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:35.974365+00:00
-- url     : https://prove2.me/theorems/33ebecfe-b205-48c2-bf6a-2d2cc69c3fd0
-- title:
--   Fun Obj: integral prod mul of split
-- statement:
--   The Fun Obj construction uses the integral prod mul of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L40-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L40-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {ι : Type*} [Fintype ι] {α β γ : ι → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
  [∀ i, MeasurableSpace (γ i)]

theorem GlobalTheory.FunObj.integral_prod_mul_of_split {μ : ∀ i, Measure (α i)} {ν : ∀ i, Measure (β i)} {ρ : ∀ i, Measure (γ i)}
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] [∀ i, SigmaFinite (ρ i)]
    {g : ∀ i, α i × β i → γ i} (hg : ∀ i, MeasurePreserving (g i) ((μ i).prod (ν i)) (ρ i))
    {p : ∀ i, γ i → α i} (hp : ∀ i, Measurable (p i)) (hpg : ∀ i a b, p i (g i (a, b)) = a)
    {F : ∀ i, γ i → ℂ} (hF : ∀ i, Integrable (F i) (ρ i))
    {H : (∀ i, α i) → ℂ} (hH : Measurable H) (hb : ∀ a, ‖H a‖ ≤ 1) :
    Integrable (fun e : ∀ i, γ i => (∏ i, F i (e i)) * H fun i => p i (e i)) (Measure.pi ρ) ∧
    Integrable (fun a : ∀ i, α i => (∏ i, ∫ b, F i (g i (a i, b)) ∂(ν i)) * H a) (Measure.pi μ) ∧
    ∫ e, (∏ i, F i (e i)) * H (fun i => p i (e i)) ∂(Measure.pi ρ) =
      ∫ a, (∏ i, ∫ b, F i (g i (a i, b)) ∂(ν i)) * H a ∂(Measure.pi μ) := by sorry
