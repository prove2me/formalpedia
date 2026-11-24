-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FourierMat_fourier_uniqueness
-- name    : GlobalTheory.CompanionTheory.FourierMat.fourier_uniqueness
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:41:17.739802+00:00
-- url     : https://prove2.me/theorems/5905e971-d31f-416a-8bff-89ffd89aadca
-- title:
--   Fourier Mat: fourier uniqueness
-- statement:
--   The Fourier Mat construction uses the fourier uniqueness property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInjectiveMatrixSpace.lean#L44-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInjectiveMatrixSpace.lean#L44-L100

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInjectiveMatrixSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Matrix FourierTransform InnerProductSpace ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FourierMat

theorem GlobalTheory.CompanionTheory.FourierMat.fourier_uniqueness : ∀ (m n : ℕ) (s : ℂ), s ≠ 0 → ∀ g : (Fin m → Fin n → ℂ) → ℂ,
    Continuous g → Integrable g →
    (∀ u : Fin m → Fin n → ℂ, ∫ v, Complex.exp (2 * Real.pi * Complex.I *
      ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v = 0) → g = 0 := by sorry
