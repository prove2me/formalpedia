-- Prove2me | Theorems.Thm_GlobalTheory_RestrMeas_isHaarProdFin_iff
-- name    : GlobalTheory.RestrMeas.isHaarProdFin_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:35.16257+00:00
-- url     : https://prove2.me/theorems/e31b0733-3813-4c3e-9356-b9e3039a32ef
-- title:
--   Restr Meas: is Haar Prod Fin iff
-- statement:
--   The Restr Meas construction uses the is Haar Prod Fin iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L230-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L230-L234

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

theorem GlobalTheory.RestrMeas.isHaarProdFin_iff : IsHaarProdFin pf K μf μ ↔ (∀ v, (μf v).IsHaarMeasure) ∧ μ.IsHaarMeasure ∧
    (∀ᶠ v in cofinite, μf v (K v) = 1) ∧
    ∀ S : Finset V, (∀ v ∉ S, μf v (K v) = 1) → ∀ B : ∀ v, Set (Yf v), (∀ v ∈ S, MeasurableSet (B v)) →
      μ {x | (∀ v ∈ S, pf v x ∈ B v) ∧ ∀ v ∉ S, pf v x ∈ K v} = ∏ v ∈ S, μf v (B v) := by sorry
