-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_charBar_apply
-- name    : GroundTheory.ProfCoh.charBar_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:52:45.370975+00:00
-- url     : https://prove2.me/theorems/6f7b86f7-3bde-4a9e-a1b5-c56a23b8a74a
-- title:
--   Prof Coh: char Bar apply
-- statement:
--   The Prof Coh construction uses the char Bar apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CyclicCupInflation.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CyclicCupInflation.lean#L91-L93

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCup
import Definitions.Def_GroundTheory_TateCohomology_InfRes
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCupInflation
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
open CategoryTheory Limits MonoidalCategory groupCohomology GroundTheory.GroupCoh
variable {G : Type} [Group G]

theorem GroundTheory.ProfCoh.charBar_apply (χ : Additive G →+ AddCircle (1 : ℚ)) (x : G) :
    charBar χ (Additive.ofMul (x : G ⧸ charKer χ)) = χ (Additive.ofMul x) := by sorry
