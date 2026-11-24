-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_trivMod_mono
-- name    : GlobalTheory.LevDesc.trivMod_mono
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:02:54.699316+00:00
-- url     : https://prove2.me/theorems/c3d31cf1-16c8-4328-8d18-cd2cf902d4cf
-- title:
--   Lev Desc: triv Mod mono
-- statement:
--   The Lev Desc construction uses the triv Mod mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L263-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L263-L264

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
variable {O : Type} [CommRing O] (N : Type) [AddCommGroup N] [Module O N]
variable {N} {I J : Ideal O}

theorem GlobalTheory.LevDesc.trivMod_mono {J' : Ideal O} (h : J ≤ J') : trivMod N I J ≤ trivMod N I J' := by sorry
