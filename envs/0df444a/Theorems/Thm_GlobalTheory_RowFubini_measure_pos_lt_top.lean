-- Prove2me | Theorems.Thm_GlobalTheory_RowFubini_measure_pos_lt_top
-- name    : GlobalTheory.RowFubini.measure_pos_lt_top
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:30:27.159726+00:00
-- url     : https://prove2.me/theorems/040f41b5-89bc-4aed-95aa-61a5be268848
-- title:
--   Row Fubini: measure pos lt top
-- statement:
--   The Row Fubini construction uses the measure pos lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L104-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L104-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise ENNReal
open GlobalTheory GlobalTheory.RowFubini
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

theorem GlobalTheory.RowFubini.measure_pos_lt_top (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (hc : IsCompact (H : Set G)) : 0 < μ H ∧ μ H < ∞ := by sorry
