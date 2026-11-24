-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_skewHermitian_add_blockTriangular
-- name    : GlobalTheory.T.exists_skewHermitian_add_blockTriangular
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:37:48.19579+00:00
-- url     : https://prove2.me/theorems/a76dfb9d-b7c2-4311-af30-bfeb5c269d2a
-- title:
--   T: exists skew Hermitian add block Triangular
-- statement:
--   The T construction uses the exists skew Hermitian add block Triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CartanDecompositionLieAlgebraStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CartanDecompositionLieAlgebraStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CartanDecompositionLieAlgebra
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CartanDecompositionLieAlgebraStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_skewHermitian_add_blockTriangular : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ), Antitone h → (∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤) → (∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) → (∀ Y ∈ 𝔤, Yᴴ = Y → Matrix.diagonal (fun i => (h i : ℂ)) * Y = Y * Matrix.diagonal (fun i => (h i : ℂ)) → Y.IsDiag) → ∀ X ∈ 𝔤, ∃ A ∈ 𝔤, ∃ B ∈ 𝔤, X = A + B ∧ Aᴴ = -A ∧ B.BlockTriangular id := by sorry
