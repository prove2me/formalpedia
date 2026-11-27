-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isCyclic_quotient_coprimeQuotientPreimage_lowerRamificationGroup
-- name    : GroundTheory.ProfCoh.isCyclic_quotient_coprimeQuotientPreimage_lowerRamificationGroup
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:45.256544+00:00
-- url     : https://prove2.me/theorems/240acd7a-ff9d-5184-8a7d-8368eb3afb1a
-- title:
--   Prof Coh: is Cyclic quotient coprime Quotient Preimage lower Ramification Group
-- statement:
--   The Prof Coh construction uses the is Cyclic quotient coprime Quotient Preimage lower Ramification Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L339-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L339-L342

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructureDefs
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_GroupStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.LocalField ValuativeRel IntermediateField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.ProfCoh.isCyclic_quotient_coprimeQuotientPreimage_lowerRamificationGroup :
    IsCyclic ((L ≃ₐ[K] L) ⧸
      coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) := by sorry
