-- Prove2me | Theorems.Thm_GlobalTheory_RestrMeas_IsRestrGroup_exists_factor
-- name    : GlobalTheory.RestrMeas.IsRestrGroup.exists_factor
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:51:58.3002+00:00
-- url     : https://prove2.me/theorems/90915d04-4400-4f5d-9851-b77c37a25b04
-- title:
--   Is Restr Group: exists factor
-- statement:
--   The Is Restr Group construction uses the exists factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L291-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L291-L334

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RestrMeas
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} [Group X] [∀ w, Group (Ya w)] [∀ v, Group (Yf v)]
  [TopologicalSpace X] [∀ w, TopologicalSpace (Ya w)] [∀ v, TopologicalSpace (Yf v)]
variable {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K K' : ∀ v, Subgroup (Yf v)}
variable [Fintype W] [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)]
variable {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ μ' : Measure X}
variable [BorelSpace X] [∀ w, BorelSpace (Ya w)] [∀ v, BorelSpace (Yf v)] [IsTopologicalGroup X]
variable [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, IsTopologicalGroup (Ya w)]
  [∀ w, LocallyCompactSpace (Ya w)] [∀ w, T2Space (Ya w)]
variable [∀ w, SecondCountableTopology (Ya w)] [∀ v, IsTopologicalGroup (Yf v)] [∀ v, LocallyCompactSpace (Yf v)]
  [∀ v, SecondCountableTopology (Yf v)]
omit [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, T2Space (Ya w)]

theorem GlobalTheory.RestrMeas.IsRestrGroup.exists_factor (h : IsRestrGroup pa pf K) (μa : ∀ w, Measure (Ya w)) (μf : ∀ v, Measure (Yf v))
    [∀ w, (μa w).IsHaarMeasure] [∀ v, (μf v).IsHaarMeasure] (ν : Measure X) [ν.IsHaarMeasure] (S : Finset V) :
    ∃ c : ℝ≥0∞, ∀ (A : ∀ w, Set (Ya w)) (B : ∀ v, Set (Yf v)), (∀ w, MeasurableSet (A w)) →
      (∀ v ∈ S, MeasurableSet (B v)) →
      ν (cyl (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) S A B) =
        c * ((∏ w, μa w (A w)) * ∏ v ∈ S, μf v (B v)) := by sorry
