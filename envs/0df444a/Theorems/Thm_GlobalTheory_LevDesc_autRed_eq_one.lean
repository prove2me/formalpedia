-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_autRed_eq_one
-- name    : GlobalTheory.LevDesc.autRed_eq_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:03:00.1398+00:00
-- url     : https://prove2.me/theorems/4a76e04f-776b-45fa-97a4-288741ea6789
-- title:
--   Lev Desc: aut Red eq one
-- statement:
--   The Lev Desc construction uses the aut Red eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L256-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L256-L261

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

theorem GlobalTheory.LevDesc.autRed_eq_one (h : I ≤ J) (γ : QAut N I) : autRed h γ = 1 ↔ γ ∈ trivMod N I J := by sorry
