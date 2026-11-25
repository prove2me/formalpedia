-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_ps_apply
-- name    : GlobalTheory.LevDesc.ps_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:09.636578+00:00
-- url     : https://prove2.me/theorems/390bd7c0-1eab-5bff-ac13-ab6de7b7236b
-- title:
--   Lev Desc: ps apply
-- statement:
--   The Lev Desc construction uses the ps apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L113-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L113-L114

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

theorem GlobalTheory.LevDesc.ps_apply (u : R) (F : G → R) : ps st u F = ∑ h, F h * st h u := by sorry
