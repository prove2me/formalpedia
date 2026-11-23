-- Prove2me | Theorems.Thm_GroundTheory_LocalField_continuous_restrictAb
-- name    : GroundTheory.LocalField.continuous_restrictAb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:28.20822+00:00
-- url     : https://prove2.me/theorems/4984498d-b95c-4697-ad43-f949df4c4d4b
-- title:
--   Local Field: continuous restrict Ab
-- statement:
--   The Local Field construction uses the continuous restrict Ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L104-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L104-L108

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

theorem GroundTheory.LocalField.continuous_restrictAb (h : E ≤ maximalAbelianExtension F Ω) : Continuous (restrictAb E h) := by sorry
