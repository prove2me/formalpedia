-- Prove2me | Theorems.Thm_GlobalTheory_norm_uniformiser_eq_inv_absNorm
-- name    : GlobalTheory.norm_uniformiser_eq_inv_absNorm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:58:32.338744+00:00
-- url     : https://prove2.me/theorems/d63306b3-47a8-5564-a908-d75dd7d2212f
-- title:
--   Global Theory: norm uniformiser eq inv abs Norm
-- statement:
--   The Global Theory construction uses the norm uniformiser eq inv abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/NormUniformiserEqInvAbsNorm.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/NormUniformiserEqInvAbsNorm.lean#L8-L19

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_NormUniformiserEqInvAbsNorm
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open NumberField IsDedekindDomain
open GlobalTheory

theorem GlobalTheory.norm_uniformiser_eq_inv_absNorm :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : v.adicCompletion F),
      Formalism.UG.IsUnifV F v ϖ → ‖ϖ‖₊ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ := by sorry
