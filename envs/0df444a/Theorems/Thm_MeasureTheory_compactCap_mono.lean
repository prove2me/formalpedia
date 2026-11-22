-- Prove2me | Theorems.Thm_MeasureTheory_compactCap_mono
-- name    : MeasureTheory.compactCap_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:31:45.814445+00:00
-- url     : https://prove2.me/theorems/9f38d9df-96ce-42a9-9cd5-d3441a9172af
-- title:
--   Measure Theory: compact Cap mono
-- statement:
--   Compact capacity is monotone in its set argument: enlarging `s` enlarges the family
--   of compact subsets and so the supremum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ChoquetCapacity.lean#L50-L56
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ChoquetCapacity.lean#L50-L56

module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ChoquetCapacity
set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Set Filter Topology

theorem MeasureTheory.compactCap_mono
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {s t : Set α} (hst : s ⊆ t) :
    MeasureTheory.compactCap μ s ≤ MeasureTheory.compactCap μ t := by sorry
