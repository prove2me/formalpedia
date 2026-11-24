-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_haar_first_column
-- name    : GlobalTheory.GLFirstColumn.haar_first_column
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:21.291815+00:00
-- url     : https://prove2.me/theorems/1845cfeb-604f-4e93-bc5e-3623e9e105d5
-- title:
--   GLFirst Column: haar first column
-- statement:
--   The GLFirst Column construction uses the haar first column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L364-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L364-L406

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.GLFirstColumn

theorem GlobalTheory.GLFirstColumn.haar_first_column : ∀ (k : ℕ), 1 ≤ k → ∃ s : (Fin (k + 1) → ℂ) → Fin (k + 1) → Fin (k + 1) → ℂ, Measurable s ∧ (∀ x, x ≠ 0 → (Matrix.of (s x)).det = 1 ∧ ∀ a, s x a 0 = x a) ∧ ∀ φ : (Fin (k + 1) → Fin (k + 1) → ℂ) → ENNReal, Measurable φ → ∫⁻ g, φ g * ENNReal.ofReal ((‖(Matrix.of g).det‖ ^ 2)⁻¹ ^ (k + 1)) = ∫⁻ x : Fin (k + 1) → ℂ, ∫⁻ h : Fin k → Fin k → ℂ, ∫⁻ T : Fin k → ℂ, φ (fun a b => (Matrix.of (Fin.cons (Fin.cons 1 (T ᵥ* Matrix.of h)) (fun a' => Fin.cons 0 (h a')) : Fin (k + 1) → Fin (k + 1) → ℂ) * (Matrix.of (s x))⁻¹) a b) * ENNReal.ofReal (‖(Matrix.of h).det‖ ^ 2 * (‖(Matrix.of h).det‖ ^ 2)⁻¹ ^ k) := by sorry
