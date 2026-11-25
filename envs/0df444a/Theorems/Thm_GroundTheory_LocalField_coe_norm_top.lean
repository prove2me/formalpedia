-- Prove2me | Theorems.Thm_GroundTheory_LocalField_coe_norm_top
-- name    : GroundTheory.LocalField.coe_norm_top
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:25.878798+00:00
-- url     : https://prove2.me/theorems/59177886-2619-4310-89df-1aa51f320e45
-- title:
--   Local Field: coe norm top
-- statement:
--   The Local Field construction uses the coe norm top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L253-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L253-L268

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
variable (L : IntermediateField K Ω)
variable [FiniteDimensional K L]

theorem GroundTheory.LocalField.coe_norm_top [(L.fixingSubgroup.subgroupOf ⊤).FiniteIndex]
    (a : fixedModule Ωˣ L.fixingSubgroup) :
    (((norm Ωˣ ⊤ L.fixingSubgroup a : fixedModule Ωˣ (⊤ : Subgroup G)) : Ωˣ) : Ω) =
      algebraMap K Ω (Algebra.norm K ((fixedModuleUnitsEquiv L a : Lˣ) : L)) := by sorry
