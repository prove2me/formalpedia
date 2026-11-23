-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_lintegral_inv
-- name    : GlobalTheory.GLFirstColumn.lintegral_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:34.817508+00:00
-- url     : https://prove2.me/theorems/8b731bdc-090f-4700-8adb-487d8aa3b25b
-- title:
--   GLFirst Column: lintegral inv
-- statement:
--   The GLFirst Column construction uses the lintegral inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L117-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L117-L212

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

theorem GlobalTheory.GLFirstColumn.lintegral_inv {m : ℕ} (f : (Fin m → Fin m → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ s, f (invM s) * wt s = ∫⁻ s, f s * wt s := by sorry
