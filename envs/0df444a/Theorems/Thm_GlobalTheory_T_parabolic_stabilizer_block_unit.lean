-- Prove2me | Theorems.Thm_GlobalTheory_T_parabolic_stabilizer_block_unit
-- name    : GlobalTheory.T.parabolic_stabilizer_block_unit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:55:21.380013+00:00
-- url     : https://prove2.me/theorems/d033da11-cfae-4063-8e67-23ba937ea7db
-- title:
--   T: parabolic stabilizer block unit
-- statement:
--   The T construction uses the parabolic stabilizer block unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraStarClosedBracketStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LieAlgebraStarClosedBracketStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraStarClosedBracket
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraStarClosedBracketStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.parabolic_stabilizer_block_unit : ∀ {n D m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin m) (Fin m) ℂ) (C : Matrix (Fin n) (Fin D) ℂ) (R : Matrix (Fin n) (Fin m) ℂ), J * J = 1 → Jᴴ = J → Cᴴ * C = 1 → Rᴴ * R = 1 → J * R = R * J' → Cᴴ * R = 0 → C * Cᴴ + J * C * Cᴴ * J + R * Rᴴ = 1 → ∀ (g : Matrix (Fin n) (Fin n) ℂ) (h : Matrix (Fin D) (Fin D) ℂ), gᴴ * J * g = J → g * C = C * h → gᴴ * C = C * hᴴ → IsUnit h ∧ g * (J * C) = (J * C) * (hᴴ)⁻¹ ∧ g * R = R * (Rᴴ * g * R) ∧ (Rᴴ * g * R)ᴴ * J' * (Rᴴ * g * R) = J' := by sorry
