-- Prove2me | Theorems.Thm_GroundTheory_LocalField_fixingOpenSubgroup_fixedField
-- name    : GroundTheory.LocalField.fixingOpenSubgroup_fixedField
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:08.786494+00:00
-- url     : https://prove2.me/theorems/77928be8-094a-416c-97ea-1e9d163d2142
-- title:
--   Local Field: fixing Open Subgroup fixed Field
-- statement:
--   The Local Field construction uses the fixing Open Subgroup fixed Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L67-L72

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

theorem GroundTheory.LocalField.fixingOpenSubgroup_fixedField (U : OpenSubgroup G) :
    fixingOpenSubgroup (fixedField (U : Subgroup G)) = U := by sorry
