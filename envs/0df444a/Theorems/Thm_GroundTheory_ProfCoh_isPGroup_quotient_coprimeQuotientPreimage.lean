-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isPGroup_quotient_coprimeQuotientPreimage
-- name    : GroundTheory.ProfCoh.isPGroup_quotient_coprimeQuotientPreimage
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:51:15.158813+00:00
-- url     : https://prove2.me/theorems/1b305362-ddb5-424f-a199-478074a0e245
-- title:
--   Prof Coh: is PGroup quotient coprime Quotient Preimage
-- statement:
--   The Prof Coh construction uses the is PGroup quotient coprime Quotient Preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L132-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L132-L141

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

theorem GroundTheory.ProfCoh.isPGroup_quotient_coprimeQuotientPreimage [Finite G] {p : ℕ} (hp : p.Prime) :
    IsPGroup p (G ⧸ coprimeQuotientPreimage N p) := by sorry
