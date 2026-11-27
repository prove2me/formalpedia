-- Prove2me | Theorems.Thm_GlobalTheory_tensorTrace_summable_sq
-- name    : GlobalTheory.tensorTrace_summable_sq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T06:13:06.395525+00:00
-- url     : https://prove2.me/theorems/54d175ab-8729-4737-9542-d915ef141337
-- title:
--   Global Theory: tensor Trace summable sq
-- statement:
--   The Global Theory construction uses the tensor Trace summable sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HilbertTensorTraceClassHasTraceProd.lean#L17-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HilbertTensorTraceClassHasTraceProd.lean#L17-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SplitHeightSummableExpNegAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousMultilinearMapExtHilbertBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsHilbertSchmidtOrthonormalApplyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumTupleProdOfSummableNormComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HilbertTensorTraceClassHasTraceProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace
noncomputable section
open GlobalTheory
open GlobalTheory.OpTrace

theorem GlobalTheory.tensorTrace_summable_sq {ι : Type} [Fintype ι] {Hs : ι → Type} [∀ i, NormedAddCommGroup (Hs i)]
    [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Ψ : ContinuousMultilinearMap ℂ Hs H) (c : ℂ)
    (hΨ : ∀ y y', ⟪Ψ y', Ψ y⟫_ℂ = c * ∏ i, ⟪y' i, y i⟫_ℂ) (A : ∀ i, Hs i →L[ℂ] Hs i)
    (hA : ∀ i, IsHilbertSchmidt (A i)) :
    Summable fun j : ∀ i, stdIndex (Hs i) => ‖Ψ (fun i => A i (stdBasis (Hs i) (j i)))‖ ^ 2 := by sorry
