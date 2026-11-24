-- Prove2me | Theorems.Thm_GlobalTheory_CMModel_mem_of_forall_ringEquiv_fixed
-- name    : GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:04:42.534603+00:00
-- url     : https://prove2.me/theorems/b46d49e7-b663-4ca1-9a64-71ab7afe7f05
-- title:
--   CMModel: mem of forall ring Equiv fixed
-- statement:
--   The CMModel construction uses the mem of forall ring Equiv fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemIntermediateFieldOfForallComplexAutFixed.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemIntermediateFieldOfForallComplexAutFixed.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemIntermediateFieldOfForallComplexAutFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMModel

theorem GlobalTheory.CMModel.mem_of_forall_ringEquiv_fixed :
    ∀ (F : IntermediateField ℚ ℂ) (x : ℂ),
      (∀ σ : ℂ ≃+* ℂ, (∀ y ∈ F, σ y = y) → σ x = x) → x ∈ F := by sorry
