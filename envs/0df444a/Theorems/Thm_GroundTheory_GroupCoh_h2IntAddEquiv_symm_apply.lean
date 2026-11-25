-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_h2IntAddEquiv_symm_apply
-- name    : GroundTheory.GroupCoh.h2IntAddEquiv_symm_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:29.108243+00:00
-- url     : https://prove2.me/theorems/345b7efa-569f-524a-aa6d-57be3bc2a4a7
-- title:
--   Group Coh: h2 Int Add Equiv symm apply
-- statement:
--   The Group Coh construction uses the h2 Int Add Equiv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Characters.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Characters.lean#L82-L85

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_Characters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology
variable (G : Type) [Group G] [Fintype G]

theorem GroundTheory.GroupCoh.h2IntAddEquiv_symm_apply (χ : Additive G →+ AddCircle (1 : ℚ)) :
    (h2IntAddEquiv G).symm χ =
      groupCohomology.δ (ratSES_shortExact G) 1 2 rfl ((h1RatModIntIso G).inv χ) := by sorry
