-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LFam_half_lt_re_of_region
-- name    : GlobalTheory.Hk.LFam.half_lt_re_of_region
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:21:18.77142+00:00
-- url     : https://prove2.me/theorems/96b8a919-f061-49b3-84a0-d9189c15159f
-- title:
--   LFam: half lt re of region
-- statement:
--   The LFam construction uses the half lt re of region property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L82-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Hk
attribute [instance] LFam.ag LFam.ft
open GlobalTheory.Hk.LFam
variable (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ)

theorem GlobalTheory.Hk.LFam.half_lt_re_of_region {c : ℝ} (hc : c ≤ 1) {s : ℂ} (hs : 1 - c / 𝓕.ell s.im ≤ s.re) : 1 / 2 < s.re := by sorry
