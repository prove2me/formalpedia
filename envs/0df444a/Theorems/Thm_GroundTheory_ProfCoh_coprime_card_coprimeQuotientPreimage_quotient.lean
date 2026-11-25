-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coprime_card_coprimeQuotientPreimage_quotient
-- name    : GroundTheory.ProfCoh.coprime_card_coprimeQuotientPreimage_quotient
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:00.650905+00:00
-- url     : https://prove2.me/theorems/d7bb4a12-73fb-4665-ba26-f73542d123de
-- title:
--   Prof Coh: coprime card coprime Quotient Preimage quotient
-- statement:
--   The Prof Coh construction uses the coprime card coprime Quotient Preimage quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L161-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L161-L186

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

theorem GroundTheory.ProfCoh.coprime_card_coprimeQuotientPreimage_quotient [Finite G] {p : ℕ} (hp : p.Prime)
    (G₀ G₁ : Subgroup G) [G₀.Normal] [G₁.Normal] (h10 : G₁ ≤ G₀) [IsCyclic (G ⧸ G₀)]
    (hG0 : (Nat.card (G₀ ⧸ G₁.subgroupOf G₀)).Coprime p) :
    (Nat.card (coprimeQuotientPreimage G₀ p ⧸
      G₁.subgroupOf (coprimeQuotientPreimage G₀ p))).Coprime p := by sorry
