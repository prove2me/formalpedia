-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_proj_eq_self_of_annihilated
-- name    : GlobalTheory.RealWeil.proj_eq_self_of_annihilated
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:16:34.713113+00:00
-- url     : https://prove2.me/theorems/78eeeafb-d072-45e4-a1dd-8deaea141691
-- title:
--   Real Weil: proj eq self of annihilated
-- statement:
--   The Real Weil construction uses the proj eq self of annihilated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProjEqSelfOfAnnihilated.lean#L266-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProjEqSelfOfAnnihilated.lean#L266-L324

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProjEqSelfOfAnnihilated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil
open Vacuum
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

theorem GlobalTheory.RealWeil.proj_eq_self_of_annihilated (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B]
    [CompleteSpace B]
    (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B) (hJ : ∀ x, J (J x) = -x)
    (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ) (f : B)
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f)
    (ha : ∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (J z) = 0) :
    _root_.GlobalTheory.RealWeil.proj h f = f := by sorry
