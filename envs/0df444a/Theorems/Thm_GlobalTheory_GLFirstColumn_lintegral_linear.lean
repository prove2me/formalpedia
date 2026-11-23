-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_lintegral_linear
-- name    : GlobalTheory.GLFirstColumn.lintegral_linear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:16.220148+00:00
-- url     : https://prove2.me/theorems/a3bbe365-5a80-406f-aa43-87061b43fbe1
-- title:
--   GLFirst Column: lintegral linear
-- statement:
--   The GLFirst Column construction uses the lintegral linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L7-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L7-L24

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

theorem GlobalTheory.GLFirstColumn.lintegral_linear {ι κ : Type} [Fintype ι] [Fintype κ]
    (L : (κ → ι → ℂ) →ₗ[ℂ] (κ → ι → ℂ)) (hL : LinearMap.det L ≠ 0)
    (F : (κ → ι → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ c, F c = ENNReal.ofReal (‖LinearMap.det L‖ ^ 2) * ∫⁻ z, F (L z) := by sorry
