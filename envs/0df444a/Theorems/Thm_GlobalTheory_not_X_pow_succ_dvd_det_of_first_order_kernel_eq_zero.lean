-- Prove2me | Theorems.Thm_GlobalTheory_not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero
-- name    : GlobalTheory.not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:54.263821+00:00
-- url     : https://prove2.me/theorems/e5fea592-8c75-49ff-9ea4-38d68a0aa686
-- title:
--   Global Theory: not X pow succ dvd det of first order kernel eq zero
-- statement:
--   The Global Theory construction uses the not X pow succ dvd det of first order kernel eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotXPowSuccDvdDetOfFirstOrderKernelEqZero.lean#L14-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotXPowSuccDvdDetOfFirstOrderKernelEqZero.lean#L14-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotXPowSuccDvdDetOfFirstOrderKernelEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero :
    ∀ (K : Type) [Field K] (a m : ℕ) (Ψ : Matrix (Fin a) (Fin a) (Polynomial K)), (∀ x0 x1 : Fin (0 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧ (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) → ¬ LinearIndependent K x0) → Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m → ¬ (Polynomial.X : Polynomial K) ^ (m + 1) ∣ Ψ.det := by sorry
