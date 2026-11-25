-- Prove2me | Theorems.Thm_GroundTheory_LocalField_coe_norm_eq_algebraMap_norm
-- name    : GroundTheory.LocalField.coe_norm_eq_algebraMap_norm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:23:10.576873+00:00
-- url     : https://prove2.me/theorems/01e3ace3-7109-45c7-9a19-ba12a186c118
-- title:
--   Local Field: coe norm eq algebra Map norm
-- statement:
--   The Local Field construction uses the coe norm eq algebra Map norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L447-L465
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L447-L465

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
variable (K' L' : Subgroup (Ω ≃ₐ[K] Ω)) {E F : IntermediateField K Ω} (hEF : E ≤ F)
  (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L')
include hK

theorem GroundTheory.LocalField.coe_norm_eq_algebraMap_norm [FiniteDimensional K F] [(L'.subgroupOf K').FiniteIndex]
    (a : fixedModule Ωˣ L') :
    (((norm Ωˣ K' L' a : fixedModule Ωˣ K') : Ωˣ) : Ω) =
      algebraMap E Ω (Algebra.norm E
        ((unitsEquivOfForall L' (extendScalars hEF) (mem_extendScalars_iff_forall L' hEF hL) a :
          (extendScalars hEF)ˣ) : extendScalars hEF)) := by sorry
