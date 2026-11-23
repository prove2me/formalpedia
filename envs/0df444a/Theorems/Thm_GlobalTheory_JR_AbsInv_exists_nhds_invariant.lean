-- Prove2me | Theorems.Thm_GlobalTheory_JR_AbsInv_exists_nhds_invariant
-- name    : GlobalTheory.JR.AbsInv.exists_nhds_invariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:24.175424+00:00
-- url     : https://prove2.me/theorems/ce76a57f-2e99-4e79-b0a8-3b3a78dea511
-- title:
--   Abs Inv: exists nhds invariant
-- statement:
--   The Abs Inv construction uses the exists nhds invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSelfDualOfDualSubgroups.lean#L13-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSelfDualOfDualSubgroups.lean#L13-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.AbsInv
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
open MeasureTheory Filter Topology Pointwise
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem GlobalTheory.JR.AbsInv.exists_nhds_invariant {f : V → ℂ}
    (hf : _root_.GlobalTheory.JR.IsTest f) :
    ∃ U ∈ 𝓝 (0 : V), ∀ M : AddSubgroup V, (M : Set V) ⊆ U → ∀ x, ∀ m ∈ M, f (x + m) = f x := by sorry
