-- Prove2me | Theorems.Thm_GlobalTheory_RestrMeas_IsHaarProd_prod_away
-- name    : GlobalTheory.RestrMeas.IsHaarProd.prod_away
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:21:06.013971+00:00
-- url     : https://prove2.me/theorems/050bd8fd-8d35-4c59-8f66-0841368eabe9
-- title:
--   Is Haar Prod: prod away
-- statement:
--   The Is Haar Prod construction uses the prod away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L396-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L396-L430

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
omit [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, IsTopologicalGroup (Ya w)] [∀ w, BorelSpace (Ya w)]
  [∀ w, LocallyCompactSpace (Ya w)] [∀ w, T2Space (Ya w)] [∀ w, SecondCountableTopology (Ya w)]

theorem GlobalTheory.RestrMeas.IsHaarProd.prod_away {S : Finset V} {pa' : ∀ w, X' →* Ya w} {pf' : ∀ v : {v // v ∉ S}, X' →* Yf v}
    {ν : Measure X'} (h : IsHaarProd pa' pf' (fun v => K v) μa (fun v => μf v) ν) [hf : ∀ v, (μf v).IsHaarMeasure]
    (hK : ∀ v, IsOpen (K v : Set (Yf v))) (e : ((∀ v : S, Yf v) × X') ≃ₜ* X)
    (ea : ∀ w p, pa w (e p) = pa' w p.2) (eS : ∀ (v : S) p, pf v (e p) = p.1 v)
    (ef : ∀ (v : {v // v ∉ S}) p, pf v (e p) = pf' v p.2) :
    IsHaarProd pa pf K μa μf (((Measure.pi fun v : S => μf v).prod ν).map e) := by sorry
