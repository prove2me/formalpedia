-- Prove2me | Theorems.Thm_GroundTheory_LocalField_injective_restrictAbPi
-- name    : GroundTheory.LocalField.injective_restrictAbPi
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:44:52.717352+00:00
-- url     : https://prove2.me/theorems/cd55bf87-20c3-4f61-9750-ba4006661770
-- title:
--   Local Field: injective restrict Ab Pi
-- statement:
--   The Local Field construction uses the injective restrict Ab Pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L208-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L208-L211

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

theorem GroundTheory.LocalField.injective_restrictAbPi : Function.Injective (restrictAbPi F Ω) := by sorry
