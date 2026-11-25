-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RayCount_aRay_eq_card
-- name    : GlobalTheory.Hk.RayCount.aRay_eq_card
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:32.451879+00:00
-- url     : https://prove2.me/theorems/18ba65c9-69d0-47b7-bc82-fcfac97442e3
-- title:
--   Ray Count: a Ray eq card
-- statement:
--   The Ray Count construction uses the a Ray eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L116-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L116-L117

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
variable {K : Type} [Field K] [NumberField K] {M : ℕ} (D : GlobalTheory.Mem.RayData K M)
open GlobalTheory.Hk.RayCount

theorem GlobalTheory.Hk.RayCount.aRay_eq_card (g : D.G) (n : ℕ) : aRay D g n = ((idealsIn_finite D g n).toFinset.card : ℝ) := by sorry
