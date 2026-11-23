-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_le_coprimeQuotientPreimage
-- name    : GroundTheory.ProfCoh.le_coprimeQuotientPreimage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:05.562423+00:00
-- url     : https://prove2.me/theorems/75f32bc5-2f29-40c8-beb4-27ebaafb3020
-- title:
--   Prof Coh: le coprime Quotient Preimage
-- statement:
--   The Prof Coh construction uses the le coprime Quotient Preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L126-L130

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
variable {G : Type*} [Group G]
variable (N : Subgroup G) [N.Normal]

theorem GroundTheory.ProfCoh.le_coprimeQuotientPreimage (p : ℕ) : N ≤ coprimeQuotientPreimage N p := by sorry
