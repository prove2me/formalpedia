-- Prove2me | Theorems.Thm_GlobalTheory_RestrMeas_IsRestrGroup_measurableSet_cyl
-- name    : GlobalTheory.RestrMeas.IsRestrGroup.measurableSet_cyl
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:20:58.557183+00:00
-- url     : https://prove2.me/theorems/9cfe3361-9f53-4cbe-a741-4ecd5d9944cc
-- title:
--   Is Restr Group: measurable Set cyl
-- statement:
--   The Is Restr Group construction uses the measurable Set cyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L238-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L238-L248

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

theorem GlobalTheory.RestrMeas.IsRestrGroup.measurableSet_cyl (h : IsRestrGroup pa pf K) {S : Finset V} {A : ∀ w, Set (Ya w)}
    {B : ∀ v, Set (Yf v)} (hA : ∀ w, MeasurableSet (A w)) (hB : ∀ v ∈ S, MeasurableSet (B v)) :
    MeasurableSet (cyl (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) S A B) := by sorry
