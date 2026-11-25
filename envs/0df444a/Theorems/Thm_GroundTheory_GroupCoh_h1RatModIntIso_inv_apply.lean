-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_h1RatModIntIso_inv_apply
-- name    : GroundTheory.GroupCoh.h1RatModIntIso_inv_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:15:52.767145+00:00
-- url     : https://prove2.me/theorems/8f3978b8-8721-5c48-938a-e99e01199959
-- title:
--   Group Coh: h1 Rat Mod Int Iso inv apply
-- statement:
--   The Group Coh construction uses the h1 Rat Mod Int Iso inv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Characters.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Characters.lean#L61-L64

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
omit [Fintype G]

theorem GroundTheory.GroupCoh.h1RatModIntIso_inv_apply (χ : Additive G →+ AddCircle (1 : ℚ)) :
    (h1RatModIntIso G).inv χ =
      H1π _ ((cocycles₁IsoOfIsTrivial (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).inv χ) := by sorry
