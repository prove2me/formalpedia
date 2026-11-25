-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_charBar_injective
-- name    : GroundTheory.ProfCoh.charBar_injective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:02:14.159822+00:00
-- url     : https://prove2.me/theorems/a96d35e7-dd19-5a2d-874a-ad73ddf2cdbf
-- title:
--   Prof Coh: char Bar injective
-- statement:
--   The Prof Coh construction uses the char Bar injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CyclicCupInflation.lean#L95-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CyclicCupInflation.lean#L95-L100

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

theorem GroundTheory.ProfCoh.charBar_injective (χ : Additive G →+ AddCircle (1 : ℚ)) :
    Function.Injective (charBar χ) := by sorry
