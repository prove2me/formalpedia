-- Prove2me | Theorems.Thm_GlobalTheory_StepData_volN_ne_zero_ne_top
-- name    : GlobalTheory.StepData.volN_ne_zero_ne_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:18.763718+00:00
-- url     : https://prove2.me/theorems/ddbb5407-11c1-4c18-9f72-db686bfd576f
-- title:
--   Step Data: vol N ne zero ne top
-- statement:
--   The Step Data construction uses the vol N ne zero ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L251-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L251-L288

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem GlobalTheory.StepData.volN_ne_zero_ne_top [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] {c : ℕ} (p : ℕ)
    {H : Subgroup (GL (n ⊕ Fin c) k)} (ho : IsOpen (H : Set (GL (n ⊕ Fin c) k)))
    (hc : IsCompact (H : Set (GL (n ⊕ Fin c) k))) :
    RootEx.volN ν n c p (H.subgroupOf (RootEx.N k n c p)) ≠ 0 ∧
      RootEx.volN ν n c p (H.subgroupOf (RootEx.N k n c p)) ≠ ⊤ := by sorry
