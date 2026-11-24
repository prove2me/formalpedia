-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_mem_trivMod
-- name    : GlobalTheory.LevDesc.mem_trivMod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:03:29.104492+00:00
-- url     : https://prove2.me/theorems/736e9460-9df5-43ea-94eb-539ea09e86f7
-- title:
--   Lev Desc: mem triv Mod
-- statement:
--   The Lev Desc construction uses the mem triv Mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L254-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L254-L254

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

theorem GlobalTheory.LevDesc.mem_trivMod {γ : QAut N I} : γ ∈ trivMod N I J ↔ ∀ q, γ q - q ∈ J • (⊤ : Submodule O (QMod N I)) := by sorry
