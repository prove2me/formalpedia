-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_finiteAbelianExtensions
-- name    : GroundTheory.LocalField.mem_finiteAbelianExtensions
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:00:19.454443+00:00
-- url     : https://prove2.me/theorems/bc308b83-764d-5267-9790-9ab95df8f97a
-- title:
--   Local Field: mem finite Abelian Extensions
-- statement:
--   The Local Field construction uses the mem finite Abelian Extensions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L192-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L192-L194

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
omit [IsGalois F Ω]

theorem GroundTheory.LocalField.mem_finiteAbelianExtensions {L : IntermediateField F Ω} :
    L ∈ finiteAbelianExtensions F Ω ↔ FiniteDimensional F L ∧ IsAbelianGalois F L := by sorry
