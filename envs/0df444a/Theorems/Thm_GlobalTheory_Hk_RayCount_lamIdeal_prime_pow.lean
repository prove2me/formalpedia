-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RayCount_lamIdeal_prime_pow
-- name    : GlobalTheory.Hk.RayCount.lamIdeal_prime_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:07:20.976576+00:00
-- url     : https://prove2.me/theorems/0d7e71f6-63e4-505a-829b-cb7ff58f0a25
-- title:
--   Ray Count: lam Ideal prime pow
-- statement:
--   The Ray Count construction uses the lam Ideal prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L122-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L122-L124

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

theorem GlobalTheory.Hk.RayCount.lamIdeal_prime_pow (P : Ideal (𝓞 K)) (hP : P.IsPrime) (h0 : P ≠ ⊥) (k : ℕ) (hk : 1 ≤ k) :
    lamIdeal (P ^ k) = Real.log (Ideal.absNorm P) := by sorry
