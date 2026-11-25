-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_mem_eigen
-- name    : GlobalTheory.LevDesc.mem_eigen
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:52.326123+00:00
-- url     : https://prove2.me/theorems/0db04536-7078-494f-bbfb-cb9ec6fb0f25
-- title:
--   Lev Desc: mem eigen
-- statement:
--   The Lev Desc construction uses the mem eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L49-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L49-L49

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

theorem GlobalTheory.LevDesc.mem_eigen {χ : G →* Kˣ} {F : R} : F ∈ eigen st χ ↔ ∀ h, st h F = ((χ h : Kˣ) : K) • F := by sorry
