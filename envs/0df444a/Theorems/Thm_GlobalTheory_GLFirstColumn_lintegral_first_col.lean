-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_lintegral_first_col
-- name    : GlobalTheory.GLFirstColumn.lintegral_first_col
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:24.72612+00:00
-- url     : https://prove2.me/theorems/dd491057-e28f-4209-a71b-002934eb0ae9
-- title:
--   GLFirst Column: lintegral first col
-- statement:
--   The GLFirst Column construction uses the lintegral first col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L278-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L278-L285

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

theorem GlobalTheory.GLFirstColumn.lintegral_first_col {n k : ℕ} (F : (Fin n → Fin (k + 1) → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, F y = ∫⁻ x : Fin n → ℂ, ∫⁻ Y : Fin n → Fin k → ℂ, F fun a => Fin.cons (x a) (Y a) := by sorry
