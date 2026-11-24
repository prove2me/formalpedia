-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FourierMat_pairing
-- name    : GlobalTheory.CompanionTheory.FourierMat.pairing
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:41:17.676674+00:00
-- url     : https://prove2.me/theorems/57c3363d-71f1-4236-9316-4b9bcd675407
-- title:
--   Fourier Mat: pairing
-- statement:
--   The Fourier Mat construction uses the pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInjectiveMatrixSpace.lean#L21-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInjectiveMatrixSpace.lean#L21-L42

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

theorem GlobalTheory.CompanionTheory.FourierMat.pairing {m n : ℕ} {s : ℂ} (hs : s ≠ 0) (w : EuclideanSpace ℂ (Fin m × Fin n))
    (v : Fin m → Fin n → ℂ) :
    (s * Matrix.trace ((Matrix.of fun a j => -(w (a, j)) / conj s)ᴴ * Matrix.of v)).re =
      -(⟪entries m n v, w⟫_ℝ) := by sorry
