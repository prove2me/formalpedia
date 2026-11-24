-- Prove2me | Theorems.Thm_GlobalTheory_RestrMeas_IsRestrGroup_subgroup
-- name    : GlobalTheory.RestrMeas.IsRestrGroup.subgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:31.263803+00:00
-- url     : https://prove2.me/theorems/a7b39074-a52e-4984-abce-b099def0bb07
-- title:
--   Is Restr Group: subgroup
-- statement:
--   The Is Restr Group construction uses the subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L145-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L145-L196

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

theorem GlobalTheory.RestrMeas.IsRestrGroup.subgroup [∀ w, T1Space (Ya w)] [∀ v, T1Space (Yf v)] (h : IsRestrGroup pa pf K)
    {W' V' : Type} {i : W' → W} {j : V' → V} (hi : Function.Injective i) (hj : Function.Injective j)
    (H : Subgroup X) (hH : ∀ x, x ∈ H ↔ (∀ w ∉ range i, pa w x = 1) ∧ ∀ v ∉ range j, pf v x = 1) :
    IsRestrGroup (fun w => (pa (i w)).comp H.subtype) (fun v => (pf (j v)).comp H.subtype) fun v => K (j v) := by sorry
