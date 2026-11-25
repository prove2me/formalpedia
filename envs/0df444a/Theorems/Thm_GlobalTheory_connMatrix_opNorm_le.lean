-- Prove2me | Theorems.Thm_GlobalTheory_connMatrix_opNorm_le
-- name    : GlobalTheory.connMatrix_opNorm_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:39.841964+00:00
-- url     : https://prove2.me/theorems/36aab197-f62b-480a-88c9-1871f23ddf2b
-- title:
--   Global Theory: conn Matrix op Norm le
-- statement:
--   The Global Theory construction uses the conn Matrix op Norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConnectionMatrixGramOperatorNormLe.lean#L117-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConnectionMatrixGramOperatorNormLe.lean#L117-L161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConnectionMatrixGramOperatorNormLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory
open GlobalTheory.ConnPointwise

theorem GlobalTheory.connMatrix_opNorm_le : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ) (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K W : ℝ), 0 < c → 0 ≤ K → 0 ≤ W → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, 0 < t i) → (∀ i x, ‖(t i • (Y⁻¹ * Bs i)) *ᵥ x‖ ≤ W * ‖x‖) → (∀ j k, ‖Dm j k‖ ≤ K) → opNorm 1 1 ((Y.map Complex.ofReal)⁻¹ * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) ≤ g * (g * K / c + W * ∑ i, ‖s i‖ / t i) := by sorry
