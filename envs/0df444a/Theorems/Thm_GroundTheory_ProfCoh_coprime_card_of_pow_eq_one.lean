-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coprime_card_of_pow_eq_one
-- name    : GroundTheory.ProfCoh.coprime_card_of_pow_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:24.596055+00:00
-- url     : https://prove2.me/theorems/267b4689-e4be-44fa-85ca-789b322b4c4f
-- title:
--   Prof Coh: coprime card of pow eq one
-- statement:
--   The Prof Coh construction uses the coprime card of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L98-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L98-L104

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

theorem GroundTheory.ProfCoh.coprime_card_of_pow_eq_one {p : ℕ} [Fact p.Prime] [Finite Q]
    (h : ∀ x : Q, x ^ p = 1 → x = 1) : (Nat.card Q).Coprime p := by sorry
