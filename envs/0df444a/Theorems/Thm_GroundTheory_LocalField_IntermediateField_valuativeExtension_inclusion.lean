-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IntermediateField_valuativeExtension_inclusion
-- name    : GroundTheory.LocalField.IntermediateField.valuativeExtension_inclusion
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:58:49.972317+00:00
-- url     : https://prove2.me/theorems/1fa19db7-4667-583e-8665-6a9be3f37588
-- title:
--   Intermediate Field: valuative Extension inclusion
-- statement:
--   The Intermediate Field construction uses the valuative Extension inclusion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/SeparableClosure.lean#L313-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/SeparableClosure.lean#L313-L320

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Topology Filter Polynomial
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [ValuativeRel Ω]

theorem GroundTheory.LocalField.IntermediateField.valuativeExtension_inclusion {E F : IntermediateField K Ω} (h : E ≤ F) :
    letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
    ValuativeExtension E F := by sorry
