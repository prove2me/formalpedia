-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_fixedModule_units_iff
-- name    : GroundTheory.LocalField.mem_fixedModule_units_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:15:24.548158+00:00
-- url     : https://prove2.me/theorems/7165eb67-85c2-53b6-b033-04093ba5f309
-- title:
--   Local Field: mem fixed Module units iff
-- statement:
--   The Local Field construction uses the mem fixed Module units iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L138-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L138-L143

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
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
local notation "G" => Ω ≃ₐ[K] Ω

theorem GroundTheory.LocalField.mem_fixedModule_units_iff (L : IntermediateField K Ω) (a : Ωˣ) :
    a ∈ fixedModule Ωˣ L.fixingSubgroup ↔ (a : Ω) ∈ L := by sorry
