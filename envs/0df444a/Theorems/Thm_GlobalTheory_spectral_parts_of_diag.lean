-- Prove2me | Theorems.Thm_GlobalTheory_spectral_parts_of_diag
-- name    : GlobalTheory.spectral_parts_of_diag
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:52.373134+00:00
-- url     : https://prove2.me/theorems/f764de3e-ac52-4d0a-a687-4aa05ee67063
-- title:
--   Global Theory: spectral parts of diag
-- statement:
--   The Global Theory construction uses the spectral parts of diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianSpectralPartsAnticommute.lean#L7-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianSpectralPartsAnticommute.lean#L7-L158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianSpectralPartsAnticommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.spectral_parts_of_diag {n : Type} [Fintype n] [DecidableEq n] (Y J U : Matrix n n ℂ)
    (μ : n → ℝ) (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1)
    (hY : Y = U * diagonal (fun j => (μ j : ℂ)) * Uᴴ) (hJ : J * Y = -(Y * J)) :
    ∃ (s : Finset ℝ) (N E : ℝ → Matrix n n ℂ), Y = ∑ ν ∈ s, (ν : ℂ) • N ν ∧
      (∀ ν, (N ν).IsHermitian ∧ (E ν).IsHermitian ∧ Y * N ν = (ν : ℂ) • E ν ∧
        N ν * Y = (ν : ℂ) • E ν ∧ Y * E ν = (ν : ℂ) • N ν ∧ E ν * Y = (ν : ℂ) • N ν ∧
        J * N ν = -(N ν * J) ∧ J * E ν = E ν * J) ∧ ∀ ν ν', E ν * E ν' = E ν' * E ν := by sorry
