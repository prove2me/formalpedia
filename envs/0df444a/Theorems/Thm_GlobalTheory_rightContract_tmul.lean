-- Prove2me | Theorems.Thm_GlobalTheory_rightContract_tmul
-- name    : GlobalTheory.rightContract_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:53.574859+00:00
-- url     : https://prove2.me/theorems/c2fee23b-f840-4430-98f7-bf5b30d7e46e
-- title:
--   Global Theory: right Contract tmul
-- statement:
--   The Global Theory construction uses the right Contract tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EigenTensorFullLeftSupport.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EigenTensorFullLeftSupport.lean#L11-L14

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

theorem GlobalTheory.rightContract_tmul {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) (x : E) (y : E') :
    rightContract l (x ⊗ₜ[F] y) = l y • x := by sorry
