-- Prove2me | Theorems.Thm_GlobalTheory_CentralIdemIntegral_isIntegral_trace_of_algClosed
-- name    : GlobalTheory.CentralIdemIntegral.isIntegral_trace_of_algClosed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:07:28.6145+00:00
-- url     : https://prove2.me/theorems/ecd42c3e-3acb-42dc-8ecc-734e16a2371a
-- title:
--   Central Idem Integral: is Integral trace of alg Closed
-- statement:
--   The Central Idem Integral construction uses the is Integral trace of alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardMulCoeffMem.lean#L7-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardMulCoeffMem.lean#L7-L42

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

theorem GlobalTheory.CentralIdemIntegral.isIntegral_trace_of_algClosed {L ι : Type} [Field L] [IsAlgClosed L] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι L) {n : ℕ} (hn : n ≠ 0) (hA : A ^ (n + 1) = A) :
    IsIntegral ℤ A.trace := by sorry
