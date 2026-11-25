-- Prove2me | Theorems.Thm_GroundTheory_LocalField_fixedField_fixingOpenSubgroup
-- name    : GroundTheory.LocalField.fixedField_fixingOpenSubgroup
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:01:50.903574+00:00
-- url     : https://prove2.me/theorems/c417e77b-cbc8-4ad4-9b78-770e7ac136eb
-- title:
--   Local Field: fixed Field fixing Open Subgroup
-- statement:
--   The Local Field construction uses the fixed Field fixing Open Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L63-L65

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomTransport
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomDictionary
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
open Abstract IntermediateField
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
local notation "G" => Ω ≃ₐ[K] Ω
variable [IsGalois K Ω]

theorem GroundTheory.LocalField.fixedField_fixingOpenSubgroup (L : IntermediateField K Ω) [FiniteDimensional K L] :
    fixedField (fixingOpenSubgroup L : Subgroup G) = L := by sorry
