-- Prove2me | Theorems.Thm_GlobalTheory_RestrMeas_IsRestrGroup_existsUnique_isHaarProd
-- name    : GlobalTheory.RestrMeas.IsRestrGroup.existsUnique_isHaarProd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:06.656104+00:00
-- url     : https://prove2.me/theorems/93f62104-af34-4911-af8a-50269e599030
-- title:
--   Is Restr Group: exists Unique is Haar Prod
-- statement:
--   The Is Restr Group construction uses the exists Unique is Haar Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L336-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L336-L368

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

theorem GlobalTheory.RestrMeas.IsRestrGroup.existsUnique_isHaarProd (h : IsRestrGroup pa pf K) (μa : ∀ w, Measure (Ya w))
    (μf : ∀ v, Measure (Yf v)) [ha : ∀ w, (μa w).IsHaarMeasure] [hf : ∀ v, (μf v).IsHaarMeasure]
    (h1 : ∀ᶠ v in cofinite, μf v (K v) = 1) : ∃! μ : Measure X, IsHaarProd pa pf K μa μf μ := by sorry
