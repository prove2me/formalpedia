-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_pow_prime_pow_mem_coprimePart
-- name    : GroundTheory.ProfCoh.exists_pow_prime_pow_mem_coprimePart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:12.059451+00:00
-- url     : https://prove2.me/theorems/399aa92d-9fd7-427c-91e4-c0b6a79cf54c
-- title:
--   Prof Coh: exists pow prime pow mem coprime Part
-- statement:
--   The Prof Coh construction uses the exists pow prime pow mem coprime Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L63-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L63-L71

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

theorem GroundTheory.ProfCoh.exists_pow_prime_pow_mem_coprimePart {p : ℕ} (hp : p.Prime) {x : Q}
    (hx : IsOfFinOrder x) : ∃ k : ℕ, x ^ p ^ k ∈ coprimePart p Q := by sorry
