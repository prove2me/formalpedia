-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_charComp_charBar
-- name    : GroundTheory.ProfCoh.charComp_charBar
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:46.245885+00:00
-- url     : https://prove2.me/theorems/08180fd6-75f5-5b82-b6c4-a30262cd1e9b
-- title:
--   Prof Coh: char Comp char Bar
-- statement:
--   The Prof Coh construction uses the char Comp char Bar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CyclicCupInflation.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CyclicCupInflation.lean#L102-L105

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

theorem GroundTheory.ProfCoh.charComp_charBar (χ : Additive G →+ AddCircle (1 : ℚ)) :
    charComp (charKer χ) (charBar χ) = χ := by sorry
