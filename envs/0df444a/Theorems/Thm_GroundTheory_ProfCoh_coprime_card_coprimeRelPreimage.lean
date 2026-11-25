-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coprime_card_coprimeRelPreimage
-- name    : GroundTheory.ProfCoh.coprime_card_coprimeRelPreimage
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:49:53.399597+00:00
-- url     : https://prove2.me/theorems/425447be-9fbe-4fe7-ab1c-6b7c707073b5
-- title:
--   Prof Coh: coprime card coprime Rel Preimage
-- statement:
--   The Prof Coh construction uses the coprime card coprime Rel Preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L222-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L222-L243

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

theorem GroundTheory.ProfCoh.coprime_card_coprimeRelPreimage [Finite G] {l p : ℕ} (hl : l.Prime) (hp : p.Prime)
    (hlp : l ≠ p) (hG1 : IsPGroup p G₁) [IsCyclic (G₀ ⧸ G₁.subgroupOf G₀)] :
    (Nat.card (coprimeRelPreimage G₀ G₁ l)).Coprime l := by sorry
