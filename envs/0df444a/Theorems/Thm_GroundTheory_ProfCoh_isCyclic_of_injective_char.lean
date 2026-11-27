-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isCyclic_of_injective_char
-- name    : GroundTheory.ProfCoh.isCyclic_of_injective_char
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:47.68562+00:00
-- url     : https://prove2.me/theorems/e21eb757-fc85-5507-bab5-a0417a1458de
-- title:
--   Prof Coh: is Cyclic of injective char
-- statement:
--   The Prof Coh construction uses the is Cyclic of injective char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CyclicCupInflation.lean#L14-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CyclicCupInflation.lean#L14-L65

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

theorem GroundTheory.ProfCoh.isCyclic_of_injective_char [Finite G] (χ : Additive G →+ AddCircle (1 : ℚ))
    (hχ : Function.Injective χ) : IsCyclic G := by sorry
