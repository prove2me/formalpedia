-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Matrixlemmas_exists_GL_vecMul_eq_single_last
-- name    : GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:06.306994+00:00
-- url     : https://prove2.me/theorems/85bc1f87-6b1b-44e8-9dc4-f4f34307946a
-- title:
--   Matrixlemmas: exists GL vec Mul eq single last
-- statement:
--   The Matrixlemmas construction uses the exists GL vec Mul eq single last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsGLVecMulEqLastBasis.lean#L7-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsGLVecMulEqLastBasis.lean#L7-L38

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsGLVecMulEqLastBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Matrixlemmas

theorem GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last {k : Type} [Field k] (n : ℕ) (ξ : Fin (n + 1) → k) (hξ : ξ ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k,
      Matrix.vecMul ξ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = Pi.single (Fin.last n) 1 := by sorry
