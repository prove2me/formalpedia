-- Prove2me | Theorems.Thm_GlobalTheory_CentralIdemIntegral_isIntegral_card_mul_coeff
-- name    : GlobalTheory.CentralIdemIntegral.isIntegral_card_mul_coeff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:07:48.686891+00:00
-- url     : https://prove2.me/theorems/0c991ccb-bb2c-4cc5-9ff6-0026aee9fccf
-- title:
--   Central Idem Integral: is Integral card mul coeff
-- statement:
--   The Central Idem Integral construction uses the is Integral card mul coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardMulCoeffMem.lean#L68-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardMulCoeffMem.lean#L68-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardMulCoeffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory GlobalTheory.CentralIdemIntegral

theorem GlobalTheory.CentralIdemIntegral.isIntegral_card_mul_coeff {G K : Type} [Group G] [Fintype G] [Field K] [CharZero K]
    (e : MonoidAlgebra K G) (he : e * e = e) (hc : ∀ x, e * x = x * e) (g : G) :
    IsIntegral ℤ ((Fintype.card G : K) * e.coeff g) := by sorry
