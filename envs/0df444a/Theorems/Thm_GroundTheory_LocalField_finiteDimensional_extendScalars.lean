-- Prove2me | Theorems.Thm_GroundTheory_LocalField_finiteDimensional_extendScalars
-- name    : GroundTheory.LocalField.finiteDimensional_extendScalars
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:17:42.347774+00:00
-- url     : https://prove2.me/theorems/7af2e6a5-06e1-4087-94d4-f56c754096ec
-- title:
--   Local Field: finite Dimensional extend Scalars
-- statement:
--   The Local Field construction uses the finite Dimensional extend Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L316-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiomDictionary.lean#L316-L319

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
omit [IsGalois K Ω]

theorem GroundTheory.LocalField.finiteDimensional_extendScalars [FiniteDimensional K F] :
    FiniteDimensional E (extendScalars hEF) := by sorry
