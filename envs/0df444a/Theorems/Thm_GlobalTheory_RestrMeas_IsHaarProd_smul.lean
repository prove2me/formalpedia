-- Prove2me | Theorems.Thm_GlobalTheory_RestrMeas_IsHaarProd_smul
-- name    : GlobalTheory.RestrMeas.IsHaarProd.smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:55.290224+00:00
-- url     : https://prove2.me/theorems/6b8a561f-30bc-4566-8114-9dae7c3a4461
-- title:
--   Is Haar Prod: smul
-- statement:
--   The Is Haar Prod construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L252-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L252-L260

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
omit [BorelSpace X] [∀ w, BorelSpace (Ya w)] [IsTopologicalGroup X]

theorem GlobalTheory.RestrMeas.IsHaarProd.smul (h : IsHaarProd pa pf K μa μf μ) (hK : ∀ v, IsOpen (K v : Set (Yf v))) (c : W → ℝ≥0)
    (d : V → ℝ≥0) (hc : ∀ w, c w ≠ 0) (hd0 : ∀ v, d v ≠ 0) (T : Finset V) (hd : ∀ v ∉ T, d v = 1) :
    IsHaarProd pa pf K (fun w => c w • μa w) (fun v => d v • μf v) (((∏ w, c w) * ∏ v ∈ T, d v) • μ) := by sorry
