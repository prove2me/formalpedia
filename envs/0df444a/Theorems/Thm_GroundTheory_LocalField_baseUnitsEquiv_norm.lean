-- Prove2me | Theorems.Thm_GroundTheory_LocalField_baseUnitsEquiv_norm
-- name    : GroundTheory.LocalField.baseUnitsEquiv_norm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:17:24.013941+00:00
-- url     : https://prove2.me/theorems/82774bd2-ced6-4d21-a8d0-808702ea5528
-- title:
--   Local Field: base Units Equiv norm
-- statement:
--   The Local Field construction uses the base Units Equiv norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L270-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L270-L275

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

theorem GroundTheory.LocalField.baseUnitsEquiv_norm [(L.fixingSubgroup.subgroupOf ⊤).FiniteIndex]
    (a : fixedModule Ωˣ L.fixingSubgroup) :
    baseUnitsEquiv (norm Ωˣ ⊤ L.fixingSubgroup a) = normUnits K L (fixedModuleUnitsEquiv L a) := by sorry
