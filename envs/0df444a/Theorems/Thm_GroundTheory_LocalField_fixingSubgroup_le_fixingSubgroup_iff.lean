-- Prove2me | Theorems.Thm_GroundTheory_LocalField_fixingSubgroup_le_fixingSubgroup_iff
-- name    : GroundTheory.LocalField.fixingSubgroup_le_fixingSubgroup_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:39.610798+00:00
-- url     : https://prove2.me/theorems/371ea32b-6670-4d7e-a315-674c325e8961
-- title:
--   Local Field: fixing Subgroup le fixing Subgroup iff
-- statement:
--   The Local Field construction uses the fixing Subgroup le fixing Subgroup iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L74-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L74-L81

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

theorem GroundTheory.LocalField.fixingSubgroup_le_fixingSubgroup_iff {L L' : IntermediateField K Ω} :
    L.fixingSubgroup ≤ L'.fixingSubgroup ↔ L' ≤ L := by sorry
