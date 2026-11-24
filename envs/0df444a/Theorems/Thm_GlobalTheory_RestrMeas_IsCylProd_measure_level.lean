-- Prove2me | Theorems.Thm_GlobalTheory_RestrMeas_IsCylProd_measure_level
-- name    : GlobalTheory.RestrMeas.IsCylProd.measure_level
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:21:12.1191+00:00
-- url     : https://prove2.me/theorems/91d101cb-9c9b-477f-a1e0-b3884fe11f9b
-- title:
--   Is Cyl Prod: measure level
-- statement:
--   The Is Cyl Prod construction uses the measure level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L81-L86

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

theorem GlobalTheory.RestrMeas.IsCylProd.measure_level (h : IsCylProd pa pf K μa μf μ) (hK : ∀ v, MeasurableSet (K v))
    {A : ∀ w, Set (Ya w)} (hA : ∀ w, MeasurableSet (A w)) :
    μ {x | (∀ w, pa w x ∈ A w) ∧ ∀ v, pf v x ∈ K v} = (∏ w, μa w (A w)) * ∏ᶠ v, μf v (K v) := by sorry
