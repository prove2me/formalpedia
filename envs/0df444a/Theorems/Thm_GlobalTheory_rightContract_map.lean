-- Prove2me | Theorems.Thm_GlobalTheory_rightContract_map
-- name    : GlobalTheory.rightContract_map
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:17:26.690084+00:00
-- url     : https://prove2.me/theorems/d709ef09-4d8c-4ba0-b8d1-1ccbe9263e8e
-- title:
--   Global Theory: right Contract map
-- statement:
--   The Global Theory construction uses the right Contract map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EigenTensorFullLeftSupport.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EigenTensorFullLeftSupport.lean#L16-L23

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

theorem GlobalTheory.rightContract_map {F : Type} [Field F] {E E' : Type} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E'] (l : E' →ₗ[F] F) (f : E →ₗ[F] E) (g : E' →ₗ[F] E')
    (w : TensorProduct F E E') :
    rightContract l (TensorProduct.map f g w) = f (rightContract (l ∘ₗ g) w) := by sorry
