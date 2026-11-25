-- Prove2me | Theorems.Thm_GlobalTheory_exists_measurable_lintegral_coset_eq_one
-- name    : GlobalTheory.exists_measurable_lintegral_coset_eq_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:01:55.883513+00:00
-- url     : https://prove2.me/theorems/5e81ea6d-49b4-4379-9503-0905e661eb4b
-- title:
--   Global Theory: exists measurable lintegral coset eq one
-- statement:
--   The Global Theory construction uses the exists measurable lintegral coset eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMeasurableLintegralCosetEqOneClosedSubgrou.lean#L11-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMeasurableLintegralCosetEqOneClosedSubgrou.lean#L11-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMeasurableLintegralCosetEqOneClosedSubgrou
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
open MeasureTheory
open scoped ENNReal
open scoped Pointwise

theorem GlobalTheory.exists_measurable_lintegral_coset_eq_one
    (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H)
    [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G) (hj : Topology.IsClosedEmbedding j) :
    ∃ b : G → ENNReal, Measurable b ∧ ∀ g, ∫⁻ h, b (j h * g) ∂ν = 1 := by sorry
