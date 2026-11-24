-- Prove2me | Theorems.Thm_GlobalTheory_JR_SelfDualUniq_fourB_const_mul
-- name    : GlobalTheory.JR.SelfDualUniq.fourB_const_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:36:04.550531+00:00
-- url     : https://prove2.me/theorems/1f05ad8e-8e6f-4f18-941d-6d7d6480865f
-- title:
--   Self Dual Uniq: four B const mul
-- statement:
--   The Self Dual Uniq construction uses the four B const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelfDualMeasureExistsUniqueFourierInversion.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelfDualMeasureExistsUniqueFourierInversion.lean#L20-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SelfDualUniq
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]

theorem GlobalTheory.JR.SelfDualUniq.fourB_const_mul (μ : Measure V) (a : ℂ) (B : V → V → ℂ) (g : V → ℂ) (y : V) :
    fourB μ B (fun z => a * g z) y = a * fourB μ B g y := by sorry
