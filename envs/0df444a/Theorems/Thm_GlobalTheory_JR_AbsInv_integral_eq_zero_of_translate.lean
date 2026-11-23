-- Prove2me | Theorems.Thm_GlobalTheory_JR_AbsInv_integral_eq_zero_of_translate
-- name    : GlobalTheory.JR.AbsInv.integral_eq_zero_of_translate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:37.628939+00:00
-- url     : https://prove2.me/theorems/be7c0888-79bc-4b42-8692-5ca1c25d5672
-- title:
--   Abs Inv: integral eq zero of translate
-- statement:
--   The Abs Inv construction uses the integral eq zero of translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSelfDualOfDualSubgroups.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSelfDualOfDualSubgroups.lean#L58-L67

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
open MeasureTheory Filter Topology Pointwise
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [MeasurableSpace V] [BorelSpace V]

theorem GlobalTheory.JR.AbsInv.integral_eq_zero_of_translate (μ : Measure V) [μ.IsAddHaarMeasure] (g : V → ℂ) (m : V) (c : ℂ)
    (hc : c ≠ 1) (h : ∀ x, g (x + m) = c * g x) : ∫ x, g x ∂μ = 0 := by sorry
