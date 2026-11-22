-- Prove2me | Theorems.Thm_MeasureTheory_MeasurableSet_compactCap_eq
-- name    : MeasureTheory.MeasurableSet.compactCap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:31:43.938808+00:00
-- url     : https://prove2.me/theorems/2ff000c9-8580-4327-a1d1-afa89b128541
-- title:
--   Measurable Set: compact Cap eq
-- statement:
--   For Borel-measurable sets, `compactCap μ s = μ s`. Two-sided bound: monotonicity
--   gives `≤`, and the existing inner regularity of finite Borel measures on Polish spaces
--   (`MeasurableSet.exists_isCompact_lt_add`) gives `≥`. The easy half of the
--   capacitability statement; the analytic-set half requires the cylinder construction in
--   the rest of the file.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ChoquetCapacity.lean#L103-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ChoquetCapacity.lean#L103-L124

module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ChoquetCapacity
set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Set Filter Topology

theorem MeasureTheory.MeasurableSet.compactCap_eq
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s) :
    MeasureTheory.compactCap μ s = μ s := by sorry
