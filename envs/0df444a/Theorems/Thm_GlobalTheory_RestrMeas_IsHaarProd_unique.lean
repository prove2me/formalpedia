-- Prove2me | Theorems.Thm_GlobalTheory_RestrMeas_IsHaarProd_unique
-- name    : GlobalTheory.RestrMeas.IsHaarProd.unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:56.800852+00:00
-- url     : https://prove2.me/theorems/8f7e714d-b352-4e53-8e37-be4766fb2a94
-- title:
--   Is Haar Prod: unique
-- statement:
--   The Is Haar Prod construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L267-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L267-L284

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
omit [∀ w, IsTopologicalGroup (Ya w)]

theorem GlobalTheory.RestrMeas.IsHaarProd.unique (hK : ∀ v, IsOpen (K v : Set (Yf v))) (hK' : ∀ v, IsCompact (K v : Set (Yf v)))
    (h : IsHaarProd pa pf K μa μf μ) (h' : IsHaarProd pa pf K μa μf μ') : μ = μ' := by sorry
