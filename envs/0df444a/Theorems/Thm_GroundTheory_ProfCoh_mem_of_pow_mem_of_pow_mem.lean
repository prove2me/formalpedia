-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_of_pow_mem_of_pow_mem
-- name    : GroundTheory.ProfCoh.mem_of_pow_mem_of_pow_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:38.814935+00:00
-- url     : https://prove2.me/theorems/ae1c7501-54ed-4095-b567-1cb496555fa4
-- title:
--   Prof Coh: mem of pow mem of pow mem
-- statement:
--   The Prof Coh construction uses the mem of pow mem of pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L84-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L84-L92

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

theorem GroundTheory.ProfCoh.mem_of_pow_mem_of_pow_mem {S : Subgroup Q} {x : Q} {a b : ℕ} (hab : a.Coprime b)
    (ha : x ^ a ∈ S) (hb : x ^ b ∈ S) : x ∈ S := by sorry
