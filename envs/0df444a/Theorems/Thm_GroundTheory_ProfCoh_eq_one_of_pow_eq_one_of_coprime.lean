-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_eq_one_of_pow_eq_one_of_coprime
-- name    : GroundTheory.ProfCoh.eq_one_of_pow_eq_one_of_coprime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:38.56533+00:00
-- url     : https://prove2.me/theorems/66e0b71b-eb6f-4f91-ba9b-30d688021aff
-- title:
--   Prof Coh: eq one of pow eq one of coprime
-- statement:
--   The Prof Coh construction uses the eq one of pow eq one of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L94-L96

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

theorem GroundTheory.ProfCoh.eq_one_of_pow_eq_one_of_coprime {p : ℕ} {x : Q} (hx : (orderOf x).Coprime p)
    (h : x ^ p = 1) : x = 1 := by sorry
