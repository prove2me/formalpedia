-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_matrix_sqrt_near_one_ultrametric
-- name    : GlobalTheory.T.exists_matrix_sqrt_near_one_ultrametric
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:49.154913+00:00
-- url     : https://prove2.me/theorems/602341b5-542f-56bb-b5d7-1a8b841e5710
-- title:
--   T: exists matrix sqrt near one ultrametric
-- statement:
--   The T construction uses the exists matrix sqrt near one ultrametric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametricStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMatrixSqrtNearOneUltrametricStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatrixSqrtNearOneUltrametric
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatrixSqrtNearOneUltrametricStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_matrix_sqrt_near_one_ultrametric : ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] (n : ℕ) (σ : K →+* K), Continuous σ → ∃ W ∈ nhds (1 : Matrix (Fin n) (Fin n) K), ∀ s ∈ W, ∃ r : Matrix (Fin n) (Fin n) K, r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K, a * s = s * a → a * r = r * a) ∧ ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by sorry
