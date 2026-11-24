-- Prove2me | Theorems.Thm_GlobalTheory_RowFubini_measure_eq_relIndex_mul
-- name    : GlobalTheory.RowFubini.measure_eq_relIndex_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:30:52.936801+00:00
-- url     : https://prove2.me/theorems/9a497fe4-8893-410a-9136-24a4053be920
-- title:
--   Row Fubini: measure eq rel Index mul
-- statement:
--   The Row Fubini construction uses the measure eq rel Index mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L68-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean#L68-L102

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

theorem GlobalTheory.RowFubini.measure_eq_relIndex_mul (μ : Measure G) [μ.IsMulLeftInvariant] (H L : Subgroup G)
    (hHL : H ≤ L) (hH : IsOpen (H : Set G)) (hL : IsCompact (L : Set G)) :
    μ L = (H.relIndex L : ℝ≥0∞) * μ H := by sorry
