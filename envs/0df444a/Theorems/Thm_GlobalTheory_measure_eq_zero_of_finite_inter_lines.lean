-- Prove2me | Theorems.Thm_GlobalTheory_measure_eq_zero_of_finite_inter_lines
-- name    : GlobalTheory.measure_eq_zero_of_finite_inter_lines
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:11:38.414796+00:00
-- url     : https://prove2.me/theorems/c5daa7db-6b4c-41ba-854e-a90257e3db80
-- title:
--   Global Theory: measure eq zero of finite inter lines
-- statement:
--   The Global Theory construction uses the measure eq zero of finite inter lines property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MeasureEqZeroOfFiniteInterLines.lean#L6-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MeasureEqZeroOfFiniteInterLines.lean#L6-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MeasureEqZeroOfFiniteInterLines
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open GlobalTheory

theorem GlobalTheory.measure_eq_zero_of_finite_inter_lines
    (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (Z : Set V) (hZ : MeasurableSet Z) (y : V)
    (h : ∀ x : V, {t : K | x + t • y ∈ Z}.Finite) : μ Z = 0 := by sorry
