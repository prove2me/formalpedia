-- Prove2me | Theorems.Thm_GlobalTheory_RestrMeas_IsHaarProd_isMulRightInvariant
-- name    : GlobalTheory.RestrMeas.IsHaarProd.isMulRightInvariant
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:24.794255+00:00
-- url     : https://prove2.me/theorems/47dce32d-5a48-4272-91c6-70863679e74a
-- title:
--   Is Haar Prod: is Mul Right Invariant
-- statement:
--   The Is Haar Prod construction uses the is Mul Right Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L372-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean#L372-L386

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
omit [∀ w, SecondCountableTopology (Ya w)] [∀ v, LocallyCompactSpace (Yf v)] [∀ v, SecondCountableTopology (Yf v)]

theorem GlobalTheory.RestrMeas.IsHaarProd.isMulRightInvariant (h : IsHaarProd pa pf K μa μf μ) (hX : IsRestrGroup pa pf K)
    [∀ w, (μa w).IsMulRightInvariant] [∀ v, (μf v).IsMulRightInvariant] : μ.IsMulRightInvariant := by sorry
