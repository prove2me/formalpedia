-- Prove2me | Theorems.Thm_GlobalTheory_JR_SelfDualUniq_fourB_nnsmul
-- name    : GlobalTheory.JR.SelfDualUniq.fourB_nnsmul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:37:23.350179+00:00
-- url     : https://prove2.me/theorems/f714c4bc-3b26-4b55-bad5-0b8204cfb8e7
-- title:
--   Self Dual Uniq: four B nnsmul
-- statement:
--   The Self Dual Uniq construction uses the four B nnsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelfDualMeasureExistsUniqueFourierInversion.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SelfDualMeasureExistsUniqueFourierInversion.lean#L15-L18

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

theorem GlobalTheory.JR.SelfDualUniq.fourB_nnsmul (μ : Measure V) (c : NNReal) (B : V → V → ℂ) (f : V → ℂ) (y : V) :
    fourB (c • μ) B f y = ((c : ℝ) : ℂ) * fourB μ B f y := by sorry
