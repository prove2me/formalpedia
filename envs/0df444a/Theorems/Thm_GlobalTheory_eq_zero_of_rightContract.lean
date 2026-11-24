-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_rightContract
-- name    : GlobalTheory.eq_zero_of_rightContract
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:18:27.880289+00:00
-- url     : https://prove2.me/theorems/e83d6638-ad04-4714-86a6-5cfb8102a2e3
-- title:
--   Global Theory: eq zero of right Contract
-- statement:
--   The Global Theory construction uses the eq zero of right Contract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EigenTensorFullLeftSupport.lean#L25-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EigenTensorFullLeftSupport.lean#L25-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EigenTensorFullLeftSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open TensorProduct

theorem GlobalTheory.eq_zero_of_rightContract {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (w : TensorProduct F E E')
    (h : ∀ l : E' →ₗ[F] F, rightContract l w = 0) : w = 0 := by sorry
