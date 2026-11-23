-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_primaryPart_iff_of_comm
-- name    : GroundTheory.ProfCoh.mem_primaryPart_iff_of_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:53.58281+00:00
-- url     : https://prove2.me/theorems/53c7acd1-679c-4908-9d2d-1ce24168460a
-- title:
--   Prof Coh: mem primary Part iff of comm
-- statement:
--   The Prof Coh construction uses the mem primary Part iff of comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L45-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L45-L61

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

theorem GroundTheory.ProfCoh.mem_primaryPart_iff_of_comm {p : ℕ} (hp : p.Prime) (hQ : ∀ a b : Q, a * b = b * a)
    {x : Q} : x ∈ primaryPart p Q ↔ ∃ n : ℕ, orderOf x = p ^ n := by sorry
