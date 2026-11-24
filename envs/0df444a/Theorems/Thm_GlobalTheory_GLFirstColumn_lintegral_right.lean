-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_lintegral_right
-- name    : GlobalTheory.GLFirstColumn.lintegral_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:42.592858+00:00
-- url     : https://prove2.me/theorems/0af401f5-868a-42a5-9556-54cc2a67826c
-- title:
--   GLFirst Column: lintegral right
-- statement:
--   The GLFirst Column construction uses the lintegral right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L26-L38

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

theorem GlobalTheory.GLFirstColumn.lintegral_right {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0)
    (F : (Fin k → Fin n → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ c, F c = ENNReal.ofReal ((‖A.det‖ ^ 2) ^ k) *
      ∫⁻ z : Fin k → Fin n → ℂ, F (fun a b => (Matrix.of z * A) a b) := by sorry
