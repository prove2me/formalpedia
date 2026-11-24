-- Prove2me | Theorems.Thm_GlobalTheory_T_normal_inv_mul_and_norm_inv_le_one
-- name    : GlobalTheory.T.normal_inv_mul_and_norm_inv_le_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:53:38.059615+00:00
-- url     : https://prove2.me/theorems/d1fddcf7-bf14-4ef2-a098-5892c0f38ca4
-- title:
--   T: normal inv mul and norm inv le one
-- statement:
--   The T construction uses the normal inv mul and norm inv le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalOfInvMulStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormalOfInvMulStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalOfInvMul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormalOfInvMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.normal_inv_mul_and_norm_inv_le_one : ∀ (F : Type) [NormedField F] [IsUltrametricDist F] (m : Type) [Fintype m] [DecidableEq m] (N : ℕ) (B : ℕ → Matrix m m F), (∀ n i j, ‖B n i j‖ ≤ 1) → (∀ n, N < n → ∀ i j, ‖B n i j‖ < 1) → ‖(B N).det‖ = 1 → Normal N (fun n => (B N)⁻¹ * B n) ∧ ∀ i j, ‖(B N)⁻¹ i j‖ ≤ 1 := by sorry
