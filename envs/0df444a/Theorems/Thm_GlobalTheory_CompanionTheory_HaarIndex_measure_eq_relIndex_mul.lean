-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HaarIndex_measure_eq_relIndex_mul
-- name    : GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:44:59.01677+00:00
-- url     : https://prove2.me/theorems/6ea2265c-fa59-4073-9ebb-5fb0141c5ce4
-- title:
--   Haar Index: measure eq rel Index mul
-- statement:
--   The Haar Index construction uses the measure eq rel Index mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarMeasureSubgroupRelIndexMul.lean#L8-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HaarMeasureSubgroupRelIndexMul.lean#L8-L54

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureSubgroupRelIndexMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HaarIndex

theorem GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul : ∀ (G : Type) [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant] (H K : AddSubgroup G), H ≤ K →
    MeasurableSet (H : Set G) → H.relIndex K ≠ 0 →
    μ (K : Set G) = (H.relIndex K : ENNReal) * μ (H : Set G) := by sorry
