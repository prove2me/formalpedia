-- Prove2me | Theorems.Thm_GlobalTheory_AvgSmooth_integrable_cont
-- name    : GlobalTheory.AvgSmooth.integrable_cont
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:34.466964+00:00
-- url     : https://prove2.me/theorems/169426b1-6af1-4377-aadd-644feab3df38
-- title:
--   Avg Smooth: integrable cont
-- statement:
--   The Avg Smooth construction uses the integrable cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ContDiffCompactAverageOfClosedPartials.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ContDiffCompactAverageOfClosedPartials.lean#L11-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ContDiffCompactAverageOfClosedPartials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.AvgSmooth
variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] {n : ℕ}

theorem GlobalTheory.AvgSmooth.integrable_cont (μ : Measure K) [IsFiniteMeasure μ] {f : K → ℂ} (hf : Continuous f) : Integrable f μ := by sorry
