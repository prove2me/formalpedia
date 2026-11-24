-- Prove2me | Theorems.Thm_GlobalTheory_JR_AbsInv_fourB_fourB
-- name    : GlobalTheory.JR.AbsInv.fourB_fourB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:05.985975+00:00
-- url     : https://prove2.me/theorems/d03de59d-1f45-4a66-9fdf-40484c801264
-- title:
--   Abs Inv: four B four B
-- statement:
--   The Abs Inv construction uses the four B four B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSelfDualOfDualSubgroups.lean#L130-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSelfDualOfDualSubgroups.lean#L130-L200

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
variable [MeasurableSpace V] [BorelSpace V]
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
open MeasureTheory Filter Topology Pointwise
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [MeasurableSpace V] [BorelSpace V]
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]

theorem GlobalTheory.JR.AbsInv.fourB_fourB (μ : Measure V) [μ.IsAddHaarMeasure] (B : V → V → ℂ)
    (hB : Continuous (fun p : V × V => B p.1 p.2)) (hs : ∀ x y, B x y = B y x)
    (ha : ∀ x x' y, B (x + x') y = B x y * B x' y) (M N : AddSubgroup V)
    (hMo : IsOpen (M : Set V)) (hNo : IsOpen (N : Set V)) (hNc : IsCompact (N : Set V))
    (hN : ∀ y, y ∈ N ↔ ∀ x ∈ M, B x y = 1) (hM : ∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1)
    (f : V → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hi : ∀ x, ∀ m ∈ M, f (x + m) = f x) (z : V) :
    _root_.GlobalTheory.JR.fourB μ B (_root_.GlobalTheory.JR.fourB μ B f) z = ((μ.real M * μ.real N : ℝ) : ℂ) * f (-z) := by sorry
