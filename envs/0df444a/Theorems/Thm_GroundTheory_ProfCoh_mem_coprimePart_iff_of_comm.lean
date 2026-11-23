-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_coprimePart_iff_of_comm
-- name    : GroundTheory.ProfCoh.mem_coprimePart_iff_of_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:24.490522+00:00
-- url     : https://prove2.me/theorems/9a0b03a4-6471-4e2a-992b-ff89c8f157c7
-- title:
--   Prof Coh: mem coprime Part iff of comm
-- statement:
--   The Prof Coh construction uses the mem coprime Part iff of comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L31-L43

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
variable {Q Q' : Type*} [Group Q] [Group Q']

theorem GroundTheory.ProfCoh.mem_coprimePart_iff_of_comm {p : ℕ} (hQ : ∀ a b : Q, a * b = b * a) {x : Q} :
    x ∈ coprimePart p Q ↔ (orderOf x).Coprime p := by sorry
