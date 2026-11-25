-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coprime_card_quotient_primaryQuotientPreimage
-- name    : GroundTheory.ProfCoh.coprime_card_quotient_primaryQuotientPreimage
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:50:54.674175+00:00
-- url     : https://prove2.me/theorems/0936947a-fa32-41c5-b627-991aa1b4ca4e
-- title:
--   Prof Coh: coprime card quotient primary Quotient Preimage
-- statement:
--   The Prof Coh construction uses the coprime card quotient primary Quotient Preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L148-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L148-L159

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

theorem GroundTheory.ProfCoh.coprime_card_quotient_primaryQuotientPreimage [Finite G] {l : ℕ} (hl : l.Prime) :
    (Nat.card (G ⧸ primaryQuotientPreimage N l)).Coprime l := by sorry
