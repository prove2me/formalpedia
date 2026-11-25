-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_card_quotient_coprimeQuotientPreimage_eq_pow
-- name    : GroundTheory.ProfCoh.exists_card_quotient_coprimeQuotientPreimage_eq_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:50:46.430202+00:00
-- url     : https://prove2.me/theorems/e2a841f6-151b-4938-84b9-8b4b650ff6e3
-- title:
--   Prof Coh: exists card quotient coprime Quotient Preimage eq pow
-- statement:
--   The Prof Coh construction uses the exists card quotient coprime Quotient Preimage eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/GroupStructure.lean#L143-L146

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

theorem GroundTheory.ProfCoh.exists_card_quotient_coprimeQuotientPreimage_eq_pow [Finite G] {p : ℕ} (hp : p.Prime) :
    ∃ a : ℕ, Nat.card (G ⧸ coprimeQuotientPreimage N p) = p ^ a := by sorry
