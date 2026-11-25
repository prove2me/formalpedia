-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RayCount_lamIdeal_of_not_prime_pow
-- name    : GlobalTheory.Hk.RayCount.lamIdeal_of_not_prime_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:07:40.121281+00:00
-- url     : https://prove2.me/theorems/6931e503-5163-4938-abc4-e53376c01cd9
-- title:
--   Ray Count: lam Ideal of not prime pow
-- statement:
--   The Ray Count construction uses the lam Ideal of not prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L126-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean#L126-L128

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

theorem GlobalTheory.Hk.RayCount.lamIdeal_of_not_prime_pow {I : Ideal (𝓞 K)}
    (h : ¬ ∃ (P : Ideal (𝓞 K)) (k : ℕ), P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ k ∧ I = P ^ k) : lamIdeal I = 0 := by sorry
