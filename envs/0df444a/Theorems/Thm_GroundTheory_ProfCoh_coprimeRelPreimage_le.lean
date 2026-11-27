-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coprimeRelPreimage_le
-- name    : GroundTheory.ProfCoh.coprimeRelPreimage_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:46.289699+00:00
-- url     : https://prove2.me/theorems/28ea6773-a6b7-4535-84ba-57b9cb52d71c
-- title:
--   Prof Coh: coprime Rel Preimage le
-- statement:
--   The Prof Coh construction uses the coprime Rel Preimage le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L192-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L192-L193

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
variable (G₀ G₁ : Subgroup G) [G₁.Normal]

theorem GroundTheory.ProfCoh.coprimeRelPreimage_le (p : ℕ) : coprimeRelPreimage G₀ G₁ p ≤ G₀ := by sorry
