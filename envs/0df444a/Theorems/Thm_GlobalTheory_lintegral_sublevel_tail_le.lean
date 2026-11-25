-- Prove2me | Theorems.Thm_GlobalTheory_lintegral_sublevel_tail_le
-- name    : GlobalTheory.lintegral_sublevel_tail_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:48:49.945459+00:00
-- url     : https://prove2.me/theorems/c60b435d-aac3-46c1-a23f-52fadefa6af3
-- title:
--   Global Theory: lintegral sublevel tail le
-- statement:
--   The Global Theory construction uses the lintegral sublevel tail le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralSublevelTailLeOfFinite.lean#L7-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralSublevelTailLeOfFinite.lean#L7-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralSublevelTailLeOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal
open GlobalTheory

theorem GlobalTheory.lintegral_sublevel_tail_le (Y : Type) [MeasurableSpace Y] (μ : Measure Y) (g : Y → ℝ≥0∞)
    (x : Y → ℝ) (hx : Measurable x) (hg : ∫⁻ y, g y ∂μ < ⊤) (_hm : Measurable g)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ T0 : ℝ, ∀ T, T0 ≤ T → ∫⁻ y in {y | x y ≤ -T + 1}, g y ∂μ ≤ ε := by sorry
