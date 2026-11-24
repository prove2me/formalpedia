-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isAbelianGalois_of_le_maximalAbelianExtension
-- name    : GroundTheory.LocalField.isAbelianGalois_of_le_maximalAbelianExtension
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:44:58.384814+00:00
-- url     : https://prove2.me/theorems/74f0220f-ace8-413b-93eb-83cd3bc65021
-- title:
--   Local Field: is Abelian Galois of le maximal Abelian Extension
-- statement:
--   The Local Field construction uses the is Abelian Galois of le maximal Abelian Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L245-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L245-L253

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

theorem GroundTheory.LocalField.isAbelianGalois_of_le_maximalAbelianExtension (E : IntermediateField F Ω) [Normal F E]
    (h : E ≤ maximalAbelianExtension F Ω) : IsAbelianGalois F E := by sorry
