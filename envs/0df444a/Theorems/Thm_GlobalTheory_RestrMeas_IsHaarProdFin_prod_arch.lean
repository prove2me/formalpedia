-- Prove2me | Theorems.Thm_GlobalTheory_RestrMeas_IsHaarProdFin_prod_arch
-- name    : GlobalTheory.RestrMeas.IsHaarProdFin.prod_arch
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:21:29.456879+00:00
-- url     : https://prove2.me/theorems/9479e90c-fee9-4c94-834f-939e4cb2f407
-- title:
--   Is Haar Prod Fin: prod arch
-- statement:
--   The Is Haar Prod Fin construction uses the prod arch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L435-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L435-L448

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
variable {X' : Type} [Group X'] [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X'] [IsTopologicalGroup X']
  [LocallyCompactSpace X'] [SecondCountableTopology X']
omit [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, T2Space (Ya w)] [∀ v, IsTopologicalGroup (Yf v)]
  [∀ v, LocallyCompactSpace (Yf v)] [∀ v, SecondCountableTopology (Yf v)] [∀ v, BorelSpace (Yf v)]

theorem GlobalTheory.RestrMeas.IsHaarProdFin.prod_arch {pf' : ∀ v, X' →* Yf v} {ν : Measure X'} (h : IsHaarProdFin pf' K μf ν)
    [ha : ∀ w, (μa w).IsHaarMeasure] (e : ((∀ w, Ya w) × X') ≃ₜ* X)
    (ea : ∀ w p, pa w (e p) = p.1 w) (ef : ∀ v p, pf v (e p) = pf' v p.2) :
    IsHaarProd pa pf K μa μf (((Measure.pi μa).prod ν).map e) := by sorry
