-- Prove2me | Theorems.Thm_GlobalTheory_T_fourier_injective_matrix_space
-- name    : GlobalTheory.T.fourier_injective_matrix_space
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:43.586739+00:00
-- url     : https://prove2.me/theorems/03eb8bae-474e-4a78-9b66-96e31ee3217e
-- title:
--   T: fourier injective matrix space
-- statement:
--   The T construction uses the fourier injective matrix space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInjectiveMatrixSpaceStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInjectiveMatrixSpaceStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInjectiveMatrixSpace
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInjectiveMatrixSpaceStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.fourier_injective_matrix_space : ∀ (m n : ℕ) (s : ℂ), s ≠ 0 → ∀ g : (Fin m → Fin n → ℂ) → ℂ, Continuous g → Integrable g → (∀ u : Fin m → Fin n → ℂ, ∫ v, Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v = 0) → g = 0 := by sorry
