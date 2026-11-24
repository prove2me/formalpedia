-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Vacuum_fderiv_norm_J
-- name    : GlobalTheory.RealWeil.Vacuum.fderiv_norm_J
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:40.399858+00:00
-- url     : https://prove2.me/theorems/d7107eab-3ce9-4f2f-a3f3-eeb0ebe31e06
-- title:
--   Vacuum: fderiv norm J
-- statement:
--   The Vacuum construction uses the fderiv norm J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProjEqSelfOfAnnihilated.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProjEqSelfOfAnnihilated.lean#L58-L67

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
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Vacuum
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}

theorem GlobalTheory.RealWeil.Vacuum.fderiv_norm_J (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (f : B) (hf : Sm ρ f)
    (ha : ∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (J z) = 0) (u z : V) :
    fderiv ℝ (fun u => (gau u)⁻¹ • ρ u f) u (J z) = I • fderiv ℝ (fun u => (gau u)⁻¹ • ρ u f) u z := by sorry
