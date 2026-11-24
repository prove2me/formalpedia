-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_trivMod_sup
-- name    : GlobalTheory.LevDesc.trivMod_sup
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:03:22.61965+00:00
-- url     : https://prove2.me/theorems/2f61c8bf-4f16-49e7-9680-f93f16d71311
-- title:
--   Lev Desc: triv Mod sup
-- statement:
--   The Lev Desc construction uses the triv Mod sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L272-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L272-L274

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

theorem GlobalTheory.LevDesc.trivMod_sup : trivMod N I (I ⊔ J) = trivMod N I J := by sorry
