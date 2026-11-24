-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_Vacuum_fderiv_norm
-- name    : GlobalTheory.RealWeil.Vacuum.fderiv_norm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:39.918905+00:00
-- url     : https://prove2.me/theorems/a4e272c8-3a2f-48d1-a49e-0a86a6d50f3d
-- title:
--   Vacuum: fderiv norm
-- statement:
--   The Vacuum construction uses the fderiv norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProjEqSelfOfAnnihilated.lean#L17-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProjEqSelfOfAnnihilated.lean#L17-L56

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

theorem GlobalTheory.RealWeil.Vacuum.fderiv_norm (h : IsHeis (omJ J) ρ) (f : B) (hf : Sm ρ f) (u z : V) :
    fderiv ℝ (fun u => (gau u)⁻¹ • ρ u f) u z =
      (gau u)⁻¹ • ρ u (fderiv ℝ (fun v => ρ v f) 0 z) +
        ((gau u)⁻¹ * (π * (⟪u, z⟫ : ℝ) - π * I * (⟪u, J z⟫ : ℝ))) • ρ u f := by sorry
