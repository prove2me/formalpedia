-- Prove2me | Theorems.Thm_MeasureTheory_measure_isChoquetCapacity
-- name    : MeasureTheory.measure_isChoquetCapacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:31:40.657686+00:00
-- url     : https://prove2.me/theorems/0f4161f8-fb88-4c2c-b93d-5ddd7ee39766
-- title:
--   Measure Theory: measure is Choquet Capacity
-- statement:
--   Every finite Borel measure on a Polish space is a Choquet capacity. Monotonicity
--   and the increasing-union axiom are immediate from `measure_mono` and `measure_iUnion`;
--   the decreasing-closed-intersection axiom uses Mathlib's `Antitone.measure_iInter` for
--   finite measures on closed sets. The instance that lets the abstract capacitability
--   machinery be applied to ordinary probability measures.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ChoquetCapacity.lean#L83-L94
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ChoquetCapacity.lean#L83-L94

module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ChoquetCapacity
set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Set Filter Topology

theorem MeasureTheory.measure_isChoquetCapacity
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ] :
    MeasureTheory.IsChoquetCapacity (fun s : Set α => μ s) := by sorry
