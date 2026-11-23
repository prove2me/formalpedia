-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LFam_two_lt_ell
-- name    : GlobalTheory.Hk.LFam.two_lt_ell
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:42.411594+00:00
-- url     : https://prove2.me/theorems/075c06a7-3071-4153-9dd6-3e3d48aa5394
-- title:
--   LFam: two lt ell
-- statement:
--   The LFam construction uses the two lt ell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L71-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L71-L80

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

theorem GlobalTheory.Hk.LFam.two_lt_ell (t : ℝ) : 2 < 𝓕.ell t := by sorry
