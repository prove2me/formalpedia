-- Prove2me | Theorems.Thm_GlobalTheory_CentralIdemIntegral_isIntegral_trace
-- name    : GlobalTheory.CentralIdemIntegral.isIntegral_trace
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:07:48.719292+00:00
-- url     : https://prove2.me/theorems/d2e5d4ef-537e-4127-9cea-47f2887e69f5
-- title:
--   Central Idem Integral: is Integral trace
-- statement:
--   The Central Idem Integral construction uses the is Integral trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardMulCoeffMem.lean#L44-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardMulCoeffMem.lean#L44-L52

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

theorem GlobalTheory.CentralIdemIntegral.isIntegral_trace {K ι : Type} [Field K] [CharZero K] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι K) {n : ℕ} (hn : n ≠ 0) (hA : A ^ (n + 1) = A) :
    IsIntegral ℤ A.trace := by sorry
