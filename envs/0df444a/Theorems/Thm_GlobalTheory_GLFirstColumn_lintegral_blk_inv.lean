-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_lintegral_blk_inv
-- name    : GlobalTheory.GLFirstColumn.lintegral_blk_inv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:32.115814+00:00
-- url     : https://prove2.me/theorems/36b70d0e-5f70-4ee2-9f1f-9859ec89a360
-- title:
--   GLFirst Column: lintegral blk inv
-- statement:
--   The GLFirst Column construction uses the lintegral blk inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L326-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L326-L362

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

theorem GlobalTheory.GLFirstColumn.lintegral_blk_inv {k : ℕ} (ψ : (Fin (k + 1) → Fin (k + 1) → ℂ) → ℝ≥0∞)
    (hψ : Measurable ψ) :
    ∫⁻ m : Fin k → Fin k → ℂ, ∫⁻ r : Fin k → ℂ, ψ (invM (blk r m)) * wt (blk r m) =
      ∫⁻ h : Fin k → Fin k → ℂ, ∫⁻ T : Fin k → ℂ, ψ (blk (T ᵥ* Matrix.of h) h) *
        ENNReal.ofReal (‖(Matrix.of h).det‖ ^ 2 * (‖(Matrix.of h).det‖ ^ 2)⁻¹ ^ k) := by sorry
