-- Prove2me | Theorems.Thm_MeasureTheory_AnalyticSet_cap_eq_iSup_isCompact
-- name    : MeasureTheory.AnalyticSet.cap_eq_iSup_isCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:31:42.132228+00:00
-- url     : https://prove2.me/theorems/0eb39b3f-f642-4989-a5ff-2f3a515d223a
-- title:
--   Analytic Set: cap eq i Sup is Compact
-- statement:
--   **Choquet capacitability**: for analytic sets, capacity = supremum over compact subsets.
--       Reference: Kechris, Classical Descriptive Set Theory, Theorem 30.13.
--
--       The proof parametrizes the analytic set as `f(ℕ^ℕ)` for continuous `f`, builds
--       `N : ℕ → ℕ` by induction using `iUnion_nat` at each coordinate, then uses
--       `iInter_closed` on the closures of cylinder images and a truncation/compactness
--       argument to show `⋂ closure(f '' Cyl N n) = f '' Bnd N` (compact).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ChoquetCapacity.lean#L295-L403
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ChoquetCapacity.lean#L295-L403

module
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ChoquetCapacity
set_option autoImplicit true
@[expose] public section
public section
universe u
open MeasureTheory Set Filter Topology

theorem MeasureTheory.AnalyticSet.cap_eq_iSup_isCompact
    {α : Type*}
    [TopologicalSpace α] [PolishSpace α]
    {cap : Set α → ENNReal}
    (hcap : MeasureTheory.IsChoquetCapacity cap)
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    cap s = ⨆ (K : Set α), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ s), cap K := by sorry
