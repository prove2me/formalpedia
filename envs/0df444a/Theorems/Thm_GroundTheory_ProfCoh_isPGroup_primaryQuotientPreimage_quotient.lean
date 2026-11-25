-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isPGroup_primaryQuotientPreimage_quotient
-- name    : GroundTheory.ProfCoh.isPGroup_primaryQuotientPreimage_quotient
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:03.784618+00:00
-- url     : https://prove2.me/theorems/e1037299-3d70-4b6f-a720-c2f6b5c36b8f
-- title:
--   Prof Coh: is PGroup primary Quotient Preimage quotient
-- statement:
--   The Prof Coh construction uses the is PGroup primary Quotient Preimage quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L247-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L247-L268

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
variable [G₀.Normal]

theorem GroundTheory.ProfCoh.isPGroup_primaryQuotientPreimage_quotient [Finite G] {l : ℕ} (hl : l.Prime)
    [IsCyclic (G ⧸ G₀)] :
    IsPGroup l (primaryQuotientPreimage G₀ l ⧸
      (coprimeRelPreimage G₀ G₁ l).subgroupOf (primaryQuotientPreimage G₀ l)) := by sorry
