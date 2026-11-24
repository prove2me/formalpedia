-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitian_spectral_projections_anticommute
-- name    : GlobalTheory.T.hermitian_spectral_projections_anticommute
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:46:05.218723+00:00
-- url     : https://prove2.me/theorems/67ade0a1-a7be-4385-931a-eec3c79ca085
-- title:
--   T: hermitian spectral projections anticommute
-- statement:
--   The T construction uses the hermitian spectral projections anticommute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianSpectralPartsAnticommuteStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianSpectralPartsAnticommuteStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianSpectralPartsAnticommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianSpectralPartsAnticommuteStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hermitian_spectral_projections_anticommute : ∀ (n : Type) [Fintype n] [DecidableEq n] (Y J : Matrix n n ℂ), Y.IsHermitian → J * Y = -(Y * J) → ∃ (s : Finset ℝ) (N E : ℝ → Matrix n n ℂ), Y = ∑ ν ∈ s, (ν : ℂ) • N ν ∧ (∀ ν, (N ν).IsHermitian ∧ (E ν).IsHermitian ∧ Y * N ν = (ν : ℂ) • E ν ∧ N ν * Y = (ν : ℂ) • E ν ∧ Y * E ν = (ν : ℂ) • N ν ∧ E ν * Y = (ν : ℂ) • N ν ∧ J * N ν = -(N ν * J) ∧ J * E ν = E ν * J) ∧ ∀ ν ν', E ν * E ν' = E ν' * E ν := by sorry
