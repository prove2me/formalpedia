-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnitaryAssembly_exists_unitary_assemble
-- name    : GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:19:35.923059+00:00
-- url     : https://prove2.me/theorems/d4a62040-8a0b-4921-bf34-a6d48270a89e
-- title:
--   Unitary Assembly: exists unitary assemble
-- statement:
--   The Unitary Assembly construction uses the exists unitary assemble property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnitaryLiftCommutingInvolution.lean#L7-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnitaryLiftCommutingInvolution.lean#L7-L58

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnitaryLiftCommutingInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnitaryAssembly

theorem GlobalTheory.CompanionTheory.UnitaryAssembly.exists_unitary_assemble : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Cᴴ * J * C = 0 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ k₀ ∈ Matrix.unitaryGroup (Fin D) ℂ, ∀ kR ∈ Matrix.unitaryGroup (Fin m) ℂ, kR * J' = J' * kR → ∃ k ∈ Matrix.unitaryGroup (Fin n) ℂ, k * J = J * k ∧ k * C = C * k₀ ∧ kᴴ * C = C * k₀ᴴ ∧ kᴴ * R = R * kRᴴ ∧ kᴴ * (J * C) = (J * C) * k₀ᴴ := by sorry
