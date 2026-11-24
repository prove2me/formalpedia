-- Prove2me | Theorems.Thm_GlobalTheory_TransportSD_map_map_equiv_right
-- name    : GlobalTheory.TransportSD.map_map_equiv_right
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:11:57.807263+00:00
-- url     : https://prove2.me/theorems/f1bdbe45-766a-44e2-9556-8136bff312ec
-- title:
--   Transport SD: map map equiv right
-- statement:
--   The Transport SD construction uses the map map equiv right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TransportSelfDualHaarMeasureKernelAddEquiv.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TransportSelfDualHaarMeasureKernelAddEquiv.lean#L14-L23

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

theorem GlobalTheory.TransportSD.map_map_equiv_right {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (T : α → β) (e : β ≃ᵐ γ) : (μ.map T).map e = μ.map (e ∘ T) := by sorry
