-- Prove2me | Theorems.Thm_GroundTheory_LocalField_restrictAb_apply
-- name    : GroundTheory.LocalField.restrictAb_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:45:03.036272+00:00
-- url     : https://prove2.me/theorems/1d049bb9-b64b-4132-80d6-c97b3b60b956
-- title:
--   Local Field: restrict Ab apply
-- statement:
--   The Local Field construction uses the restrict Ab apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L96-L102

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open IntermediateField
open scoped commutatorElement
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (E : IntermediateField F Ω) [Normal F E]

theorem GroundTheory.LocalField.restrictAb_apply (h : E ≤ maximalAbelianExtension F Ω) (σ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω) (x : E) :
    ((restrictAb E h σ x : E) : Ω) = ((σ ⟨x, h x.2⟩ : maximalAbelianExtension F Ω) : Ω) := by sorry
