-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_groupMat_apply
-- name    : GlobalTheory.LevDesc.groupMat_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:06.032157+00:00
-- url     : https://prove2.me/theorems/b09ddadd-47da-4791-ad7e-bbea3181039b
-- title:
--   Lev Desc: group Mat apply
-- statement:
--   The Lev Desc construction uses the group Mat apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L41-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L41-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {G K R : Type} [Group G] [Field K] [CommRing R] [Algebra K R]
variable (st : G → R →ₐ[K] R)

theorem GlobalTheory.LevDesc.groupMat_apply (u : R) (h g : G) : groupMat st u h g = st (h * g) u := by sorry
