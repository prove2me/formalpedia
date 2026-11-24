-- Prove2me | Theorems.Thm_GlobalTheory_WeilTr_isUWeilB_trRep
-- name    : GlobalTheory.WeilTr.isUWeilB_trRep
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:55:01.187125+00:00
-- url     : https://prove2.me/theorems/3be12e2f-6023-4121-bce7-d4ff319f08fe
-- title:
--   Weil Tr: is UWeil B tr Rep
-- statement:
--   The Weil Tr construction uses the is UWeil B tr Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUSplittingTrRep.lean#L99-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsUSplittingTrRep.lean#L99-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUSplittingTrRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.WeilTr
open GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]
variable [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R}

theorem GlobalTheory.WeilTr.isUWeilB_trRep {R : Type} [CommRing R] [Invertible (2 : R)] [TopologicalSpace R] {E : Type} [CommRing E] [Algebra R E]
    [TopologicalSpace E] [IsModuleTopology R E]
    {c : E →ₐ[R] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {κ : Type} [Fintype κ]
    {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
    {T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)} (hT : IsGoodInt C ψ d d₁ T) (hD : HasDbl c C ψ ξ JA JB d d₁ T)
    {χ : Eˣ →* Circle} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUWeilB c C ψ ξ JA JB d χ om) : IsUWeilB c C ψ ξ JA JB d₁ χ (trRep T om) := by sorry
