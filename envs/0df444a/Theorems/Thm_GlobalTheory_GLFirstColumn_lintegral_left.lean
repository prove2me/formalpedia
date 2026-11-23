-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_lintegral_left
-- name    : GlobalTheory.GLFirstColumn.lintegral_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:27.868913+00:00
-- url     : https://prove2.me/theorems/46cd7960-b90c-47d1-a8a8-93b1614cb0e3
-- title:
--   GLFirst Column: lintegral left
-- statement:
--   The GLFirst Column construction uses the lintegral left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L40-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L40-L60

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

theorem GlobalTheory.GLFirstColumn.lintegral_left {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0)
    (F : (Fin n → Fin k → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ c, F c = ENNReal.ofReal ((‖A.det‖ ^ 2) ^ k) *
      ∫⁻ z : Fin n → Fin k → ℂ, F (fun a b => (A * Matrix.of z) a b) := by sorry
