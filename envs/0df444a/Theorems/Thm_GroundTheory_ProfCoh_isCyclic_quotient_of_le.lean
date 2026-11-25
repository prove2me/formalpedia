-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isCyclic_quotient_of_le
-- name    : GroundTheory.ProfCoh.isCyclic_quotient_of_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:13.832839+00:00
-- url     : https://prove2.me/theorems/68748399-a64e-4250-a32e-e3915b067019
-- title:
--   Prof Coh: is Cyclic quotient of le
-- statement:
--   The Prof Coh construction uses the is Cyclic quotient of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L112-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L112-L116

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

theorem GroundTheory.ProfCoh.isCyclic_quotient_of_le {M N : Subgroup G} [M.Normal] [N.Normal] (h : M ≤ N)
    [IsCyclic (G ⧸ M)] : IsCyclic (G ⧸ N) := by sorry
