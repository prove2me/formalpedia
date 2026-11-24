-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FrameSort_exists_antitone_reorder
-- name    : GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:41:24.323719+00:00
-- url     : https://prove2.me/theorems/b01fc463-ff18-4b8c-9d33-bc68c7ef1257
-- title:
--   Frame Sort: exists antitone reorder
-- statement:
--   The Frame Sort construction uses the exists antitone reorder property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AntitoneDiagonalConjugate.lean#L6-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AntitoneDiagonalConjugate.lean#L6-L39

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AntitoneDiagonalConjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrameSort

theorem GlobalTheory.CompanionTheory.FrameSort.exists_antitone_reorder : ∀ {n : ℕ} (U₀ : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), U₀ ∈ Matrix.unitaryGroup (Fin n) ℂ → ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ h : Fin n → ℝ, Antitone h ∧ U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ = U₀ * Matrix.diagonal (fun i => (d i : ℂ)) * U₀ᴴ ∧ ∀ Z : Matrix (Fin n) (Fin n) ℂ, (U₀ᴴ * Z * U₀).IsDiag → (Uᴴ * Z * U).IsDiag := by sorry
