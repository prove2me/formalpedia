-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnitaryBlock_block_diagonal_of_keeps_frame
-- name    : GlobalTheory.CompanionTheory.UnitaryBlock.block_diagonal_of_keeps_frame
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:19:52.466935+00:00
-- url     : https://prove2.me/theorems/db031749-9580-4e3d-83ce-39243a116d11
-- title:
--   Unitary Block: block diagonal of keeps frame
-- statement:
--   The Unitary Block construction uses the block diagonal of keeps frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraStarClosedBracket.lean#L7-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraStarClosedBracket.lean#L7-L90

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraStarClosedBracket
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnitaryBlock

theorem GlobalTheory.CompanionTheory.UnitaryBlock.block_diagonal_of_keeps_frame : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)
    (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ)
    (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Rᴴ * R = 1 →
    J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 →
    ∀ (g : Matrix (Fin n) (Fin n) ℂ) (h : Matrix (Fin D) (Fin D) ℂ), gᴴ * J * g = J →
    g * C = C * h → gᴴ * C = C * hᴴ →
    IsUnit h ∧ g * (J * C) = (J * C) * (hᴴ)⁻¹ ∧ g * R = R * (Rᴴ * g * R) ∧
      (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R) = J' := by sorry
