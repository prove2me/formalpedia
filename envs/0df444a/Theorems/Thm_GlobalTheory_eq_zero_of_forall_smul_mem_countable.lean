-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_forall_smul_mem_countable
-- name    : GlobalTheory.eq_zero_of_forall_smul_mem_countable
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:29:34.692802+00:00
-- url     : https://prove2.me/theorems/dffbf835-9a60-4eb0-99aa-22f6acc740a2
-- title:
--   Global Theory: eq zero of forall smul mem countable
-- statement:
--   The Global Theory construction uses the eq zero of forall smul mem countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/SmulPeriodMapMkZeroFstEqNegForm.lean#L11-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.eq_zero_of_forall_smul_mem_countable {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Set V}
    (hS : S.Countable) {z : V} (hz : ∀ s : ℂ, s • z ∈ S) : z = 0 := by sorry
