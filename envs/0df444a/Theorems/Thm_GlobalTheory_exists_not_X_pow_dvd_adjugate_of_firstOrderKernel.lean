-- Prove2me | Theorems.Thm_GlobalTheory_exists_not_X_pow_dvd_adjugate_of_firstOrderKernel
-- name    : GlobalTheory.exists_not_X_pow_dvd_adjugate_of_firstOrderKernel
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:26.205674+00:00
-- url     : https://prove2.me/theorems/855e4080-f111-4b8a-a341-9cdf782010f1
-- title:
--   Global Theory: exists not X pow dvd adjugate of first Order Kernel
-- statement:
--   The Global Theory construction uses the exists not X pow dvd adjugate of first Order Kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean#L195-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsNotXPowDvdAdjugateOfFirstOrderKernel.lean#L195-L237

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory
open CofactorOrder

theorem GlobalTheory.exists_not_X_pow_dvd_adjugate_of_firstOrderKernel (K : Type) [Field K] (a m : ℕ)
    (Ψ : Matrix (Fin a) (Fin a) (Polynomial K))
    (H : ∀ x0 x1 : Fin (1 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧
      (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) →
      ¬ LinearIndependent K x0)
    (hν : Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m + 1)
    (ha : a ≠ 0) :
    ∃ b c, ¬ (Polynomial.X : Polynomial K) ^ (2 * m + 1) ∣ Ψ.adjugate b c := by sorry
