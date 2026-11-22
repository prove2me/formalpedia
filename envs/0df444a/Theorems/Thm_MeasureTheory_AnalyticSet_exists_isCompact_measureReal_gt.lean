-- Prove2me | Theorems.Thm_MeasureTheory_AnalyticSet_exists_isCompact_measureReal_gt
-- name    : MeasureTheory.AnalyticSet.exists_isCompact_measureReal_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:32:11.97832+00:00
-- url     : https://prove2.me/theorems/51ea2327-bb6f-43dc-a837-9d9f0537513a
-- title:
--   Analytic Set: exists is Compact measure Real gt
-- statement:
--   Inner regularity for analytic sets: every analytic subset of a Polish space can be
--   approximated from inside by a compact subset, in measure. For any finite Borel measure
--   `μ`, any analytic `s`, and any `r < μ.real s`, there is a compact `K ⊆ s` with
--   `μ.real K > r`. The Choquet capacitability theorem (Kechris 30.13), specialised to the
--   measure-as-capacity instance.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/AnalyticMeasurability.lean#L33-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/AnalyticMeasurability.lean#L33-L77

module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ChoquetCapacity
public import Mathlib.MeasureTheory.Measure.Real
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_AnalyticMeasurability
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set

theorem MeasureTheory.AnalyticSet.exists_isCompact_measureReal_gt
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    ∀ ε > 0, ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ μ.real s < μ.real K + ε := by sorry
