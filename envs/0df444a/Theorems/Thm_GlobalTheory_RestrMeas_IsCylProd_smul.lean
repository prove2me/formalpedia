-- Prove2me | Theorems.Thm_GlobalTheory_RestrMeas_IsCylProd_smul
-- name    : GlobalTheory.RestrMeas.IsCylProd.smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:24.477958+00:00
-- url     : https://prove2.me/theorems/7a508e59-de79-4378-9bf4-94413d5cd1a5
-- title:
--   Is Cyl Prod: smul
-- statement:
--   The Is Cyl Prod construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L88-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L88-L98

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
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type}
variable {pa : ∀ w, X → Ya w} {pf : ∀ v, X → Yf v} {K K' : ∀ v, Set (Yf v)}
variable [Fintype W] [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)]
variable {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ : Measure X}

theorem GlobalTheory.RestrMeas.IsCylProd.smul (h : IsCylProd pa pf K μa μf μ) (hK : ∀ v, MeasurableSet (K v)) (c : W → ℝ≥0∞)
    (d : V → ℝ≥0∞) (T : Finset V) (hd : ∀ v ∉ T, d v = 1) :
    IsCylProd pa pf K (fun w => c w • μa w) (fun v => d v • μf v) (((∏ w, c w) * ∏ v ∈ T, d v) • μ) := by sorry
