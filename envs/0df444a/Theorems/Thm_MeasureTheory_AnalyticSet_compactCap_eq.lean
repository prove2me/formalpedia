-- Prove2me | Theorems.Thm_MeasureTheory_AnalyticSet_compactCap_eq
-- name    : MeasureTheory.AnalyticSet.compactCap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:31:46.459801+00:00
-- url     : https://prove2.me/theorems/e529275f-1dc2-4d82-82d0-22daa3315376
-- title:
--   Analytic Set: compact Cap eq
-- statement:
--   For analytic sets, compact capacity = measure.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ChoquetCapacity.lean#L408-L415
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ChoquetCapacity.lean#L408-L415

module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ChoquetCapacity
set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Set Filter Topology

theorem MeasureTheory.AnalyticSet.compactCap_eq
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    MeasureTheory.compactCap μ s = μ s := by sorry
