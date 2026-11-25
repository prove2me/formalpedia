-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RayCount_coe_aRay_eq_cnt
-- name    : GlobalTheory.Hk.RayCount.coe_aRay_eq_cnt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:26.209803+00:00
-- url     : https://prove2.me/theorems/8c5bc93c-bf29-5633-8a6e-5c0a226ae4df
-- title:
--   Ray Count: coe a Ray eq cnt
-- statement:
--   The Ray Count construction uses the coe a Ray eq cnt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L111-L114

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

theorem GlobalTheory.Hk.RayCount.coe_aRay_eq_cnt (g : D.G) {n : ℕ} (hn : n ≠ 0) : (aRay D g n : ℂ) = D.cnt g n := by sorry
