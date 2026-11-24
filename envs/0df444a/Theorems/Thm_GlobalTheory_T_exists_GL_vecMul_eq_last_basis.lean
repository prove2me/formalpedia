-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_GL_vecMul_eq_last_basis
-- name    : GlobalTheory.T.exists_GL_vecMul_eq_last_basis
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:32:59.394794+00:00
-- url     : https://prove2.me/theorems/ba89f0fc-3675-4fcb-823f-5e97feb6b467
-- title:
--   T: exists GL vec Mul eq last basis
-- statement:
--   The T construction uses the exists GL vec Mul eq last basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsGLVecMulEqLastBasisStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsGLVecMulEqLastBasisStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsGLVecMulEqLastBasis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsGLVecMulEqLastBasisStatement
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

theorem GlobalTheory.T.exists_GL_vecMul_eq_last_basis : ∀ {k : Type} [Field k] (n : ℕ) (ξ : Fin (n + 1) → k), ξ ≠ 0 → ∃ g : GL (Fin (n + 1)) k, Matrix.vecMul ξ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = Pi.single (Fin.last n) 1 := by sorry
