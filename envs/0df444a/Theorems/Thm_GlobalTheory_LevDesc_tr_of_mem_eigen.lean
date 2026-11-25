-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_tr_of_mem_eigen
-- name    : GlobalTheory.LevDesc.tr_of_mem_eigen
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:33.037747+00:00
-- url     : https://prove2.me/theorems/df3a9a99-c9a8-47c3-b3c8-1265f829ca65
-- title:
--   Lev Desc: tr of mem eigen
-- statement:
--   The Lev Desc construction uses the tr of mem eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L124-L126

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
variable [Fintype G]

theorem GlobalTheory.LevDesc.tr_of_mem_eigen {χ : G →* Kˣ} {F : R} (hF : F ∈ eigen st χ) : tr st χ F = (Fintype.card G : K) • F := by sorry
