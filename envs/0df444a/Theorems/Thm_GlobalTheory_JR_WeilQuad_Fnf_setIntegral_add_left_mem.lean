-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_Fnf_setIntegral_add_left_mem
-- name    : GlobalTheory.JR.WeilQuad.Fnf.setIntegral_add_left_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:39:12.073624+00:00
-- url     : https://prove2.me/theorems/fa0ac313-22ea-46b8-8fdc-bacfb7e7d06a
-- title:
--   Fnf: set Integral add left mem
-- statement:
--   The Fnf construction uses the set Integral add left mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFOpNOpFOpGauss.lean#L74-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilFOpNOpFOpGauss.lean#L74-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFOpNOpFOpGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.Fnf

theorem GlobalTheory.JR.WeilQuad.Fnf.setIntegral_add_left_mem {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddLeftInvariant] (Λ : AddSubgroup V)
    (hΛ : MeasurableSet (Λ : Set V)) (g : V → ℂ) (w : V) (hw : w ∈ Λ) :
    ∫ y in (Λ : Set V), g (w + y) ∂μ = ∫ y in (Λ : Set V), g y ∂μ := by sorry
