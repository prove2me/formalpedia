-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_lowerRamificationGroup_one_le_coprimeQuotientPreimage
-- name    : GroundTheory.ProfCoh.lowerRamificationGroup_one_le_coprimeQuotientPreimage
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:03:16.707787+00:00
-- url     : https://prove2.me/theorems/5d77b7c0-e068-41b6-8959-e188a73b27e8
-- title:
--   Prof Coh: lower Ramification Group one le coprime Quotient Preimage
-- statement:
--   The Prof Coh construction uses the lower Ramification Group one le coprime Quotient Preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L334-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L334-L337

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

theorem GroundTheory.ProfCoh.lowerRamificationGroup_one_le_coprimeQuotientPreimage :
    lowerRamificationGroup K L 1 ≤
      coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K]) := by sorry
