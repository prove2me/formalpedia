-- Prove2me | Theorems.Thm_GlobalTheory_T_rightInvariant_GL_of_upperTriangular_rightInvariant
-- name    : GlobalTheory.T.rightInvariant_GL_of_upperTriangular_rightInvariant
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:15.805268+00:00
-- url     : https://prove2.me/theorems/b872a233-474a-5d56-92a1-8635be7383bb
-- title:
--   T: right Invariant GL of upper Triangular right Invariant
-- statement:
--   The T construction uses the right Invariant GL of upper Triangular right Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightInvariantGLOfUpperTriangularRightInvariantStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightInvariantGLOfUpperTriangularRightInvariantStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariant
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.rightInvariant_GL_of_upperTriangular_rightInvariant : ∀ {k : Type} [Field k] [Infinite k] {m : ℕ} (ψ Φ : Matrix (Fin m) (Fin m) k → k) (r : k → k), (∀ A₀ D : Matrix (Fin m) (Fin m) k, ∃ p : Polynomial k, ∀ x : k, Φ (A₀ + x • D) = p.eval x) → (∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ A = r A.det * Φ A) → (∀ A T : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id → ψ (A * T) = ψ A) → ∀ A B : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → B.det ≠ 0 → ψ (A * B) = ψ A := by sorry
