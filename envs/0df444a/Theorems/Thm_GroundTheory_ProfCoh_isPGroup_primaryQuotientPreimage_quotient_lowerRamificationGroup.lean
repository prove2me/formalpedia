-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isPGroup_primaryQuotientPreimage_quotient_lowerRamificationGroup
-- name    : GroundTheory.ProfCoh.isPGroup_primaryQuotientPreimage_quotient_lowerRamificationGroup
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:03:46.904941+00:00
-- url     : https://prove2.me/theorems/fa45d9d3-3ec9-4d3a-9fb7-0cbf43eea6e4
-- title:
--   Prof Coh: is PGroup primary Quotient Preimage quotient lower Ramification Group
-- statement:
--   The Prof Coh construction uses the is PGroup primary Quotient Preimage quotient lower Ramification Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L376-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L376-L381

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

theorem GroundTheory.ProfCoh.isPGroup_primaryQuotientPreimage_quotient_lowerRamificationGroup {l : ℕ}
    (hl : l.Prime) :
    IsPGroup l (primaryQuotientPreimage (lowerRamificationGroup K L 0) l ⧸
      (coprimeRelPreimage (lowerRamificationGroup K L 0) (lowerRamificationGroup K L 1) l).subgroupOf
        (primaryQuotientPreimage (lowerRamificationGroup K L 0) l)) := by sorry
