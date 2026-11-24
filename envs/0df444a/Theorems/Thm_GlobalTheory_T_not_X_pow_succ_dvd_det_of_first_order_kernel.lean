-- Prove2me | Theorems.Thm_GlobalTheory_T_not_X_pow_succ_dvd_det_of_first_order_kernel
-- name    : GlobalTheory.T.not_X_pow_succ_dvd_det_of_first_order_kernel
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:53:43.555471+00:00
-- url     : https://prove2.me/theorems/4a42c11c-f388-40c8-b943-c6297eda643d
-- title:
--   T: not X pow succ dvd det of first order kernel
-- statement:
--   The T construction uses the not X pow succ dvd det of first order kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotXPowSuccDvdDetOfFirstOrderKernelEqZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotXPowSuccDvdDetOfFirstOrderKernelEqZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotXPowSuccDvdDetOfFirstOrderKernelEqZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotXPowSuccDvdDetOfFirstOrderKernelEqZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.not_X_pow_succ_dvd_det_of_first_order_kernel : ∀ (K : Type) [Field K] (a m : ℕ) (Ψ : Matrix (Fin a) (Fin a) (Polynomial K)), (∀ x0 x1 : Fin (0 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧ (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) → ¬ LinearIndependent K x0) → Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m → ¬ (Polynomial.X : Polynomial K) ^ (m + 1) ∣ Ψ.det := by sorry
