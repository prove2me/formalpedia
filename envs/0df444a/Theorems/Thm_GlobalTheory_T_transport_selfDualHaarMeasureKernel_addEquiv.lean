-- Prove2me | Theorems.Thm_GlobalTheory_T_transport_selfDualHaarMeasureKernel_addEquiv
-- name    : GlobalTheory.T.transport_selfDualHaarMeasureKernel_addEquiv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:59:59.511175+00:00
-- url     : https://prove2.me/theorems/6d30fbc2-882e-467c-93da-e9ca9bb28392
-- title:
--   T: transport self Dual Haar Measure Kernel add Equiv
-- statement:
--   The T construction uses the transport self Dual Haar Measure Kernel add Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TransportSelfDualHaarMeasureKernelAddEquivStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TransportSelfDualHaarMeasureKernelAddEquivStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TransportSelfDualHaarMeasureKernelAddEquiv
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TransportSelfDualHaarMeasureKernelAddEquivStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.transport_selfDualHaarMeasureKernel_addEquiv : ∀ {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] (h : V' ≃+ V), Continuous h → Continuous h.symm → ∀ (μ : Measure V) (B : V → V → ℂ), (SelfDual μ B → SelfDual (Measure.map h.symm μ) (fun x y => B (h x) (h y))) ∧ ∀ (f : V' → ℂ) (y : V'), fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y = fourB μ B (fun v => f (h.symm v)) (h y) := by sorry
