-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RayCount_lamRay_eq_sum
-- name    : GlobalTheory.Hk.RayCount.lamRay_eq_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:07:33.373018+00:00
-- url     : https://prove2.me/theorems/f0e034ab-a756-4013-bd9a-150fb5b76e0c
-- title:
--   Ray Count: lam Ray eq sum
-- statement:
--   The Ray Count construction uses the lam Ray eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L119-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L119-L120

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

theorem GlobalTheory.Hk.RayCount.lamRay_eq_sum (g : D.G) (n : ℕ) : lamRay D g n = ∑ I ∈ (idealsIn_finite D g n).toFinset, lamIdeal I := by sorry
