-- Prove2me | Theorems.Thm_GlobalTheory_T_wittVector_gaussNorm_mul
-- name    : GlobalTheory.T.wittVector_gaussNorm_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:39:50.852278+00:00
-- url     : https://prove2.me/theorems/1d185320-0211-41ed-b0f1-735ca807d223
-- title:
--   T: witt Vector gauss Norm mul
-- statement:
--   The T construction uses the witt Vector gauss Norm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormMulStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorGaussNormMulStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.wittVector_gaussNorm_mul : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ), (∀ x, 0 ≤ a x ∧ a x ≤ 1) → a 0 = 0 → a 1 = 1 → (∀ x y, a (x * y) = a x * a y) → (∀ x y, a (x + y) ≤ max (a x) (a y)) → ∀ r : ℝ, 0 < r → r < 1 → ∀ N : WittVector l R → ℝ, (∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ x y, N (x * y) = N x * N y := by sorry
