-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_coprime_pow_mem_primaryPart
-- name    : GroundTheory.ProfCoh.exists_coprime_pow_mem_primaryPart
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:59.736398+00:00
-- url     : https://prove2.me/theorems/5b40a4b3-2f4e-4bd1-b11f-5f3cba4659de
-- title:
--   Prof Coh: exists coprime pow mem primary Part
-- statement:
--   The Prof Coh construction uses the exists coprime pow mem primary Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L73-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L73-L82

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

theorem GroundTheory.ProfCoh.exists_coprime_pow_mem_primaryPart {p : ℕ} (hp : p.Prime) {x : Q}
    (hx : IsOfFinOrder x) : ∃ m : ℕ, m.Coprime p ∧ x ^ m ∈ primaryPart p Q := by sorry
