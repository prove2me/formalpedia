-- Prove2me | Theorems.Thm_GlobalTheory_TransportSD_map_map_equiv_left
-- name    : GlobalTheory.TransportSD.map_map_equiv_left
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:11:57.823839+00:00
-- url     : https://prove2.me/theorems/97705c8e-6374-4897-937f-38466aadf5a8
-- title:
--   Transport SD: map map equiv left
-- statement:
--   The Transport SD construction uses the map map equiv left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TransportSelfDualHaarMeasureKernelAddEquiv.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TransportSelfDualHaarMeasureKernelAddEquiv.lean#L7-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TransportSelfDualHaarMeasureKernelAddEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.TransportSD

theorem GlobalTheory.TransportSD.map_map_equiv_left {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (e : α ≃ᵐ β) (g : β → γ) : (μ.map e).map g = μ.map (g ∘ e) := by sorry
