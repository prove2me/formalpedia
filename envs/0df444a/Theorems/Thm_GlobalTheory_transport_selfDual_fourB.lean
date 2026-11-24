-- Prove2me | Theorems.Thm_GlobalTheory_transport_selfDual_fourB
-- name    : GlobalTheory.transport_selfDual_fourB
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:23:40.075562+00:00
-- url     : https://prove2.me/theorems/f2690f84-8968-45e7-8f75-d9d0d96a79ef
-- title:
--   Global Theory: transport self Dual four B
-- statement:
--   The Global Theory construction uses the transport self Dual four B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TransportSelfDualHaarMeasureKernelAddEquiv.lean#L28-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TransportSelfDualHaarMeasureKernelAddEquiv.lean#L28-L78

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
open GlobalTheory.TransportSD

theorem GlobalTheory.transport_selfDual_fourB : ∀ {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [MeasurableSpace V'] [BorelSpace V'] (h : V' ≃+ V), Continuous h → Continuous h.symm → ∀ (μ : Measure V) (B : V → V → ℂ), (SelfDual μ B → SelfDual (Measure.map h.symm μ) (fun x y => B (h x) (h y))) ∧ ∀ (f : V' → ℂ) (y : V'), fourB (Measure.map h.symm μ) (fun x y => B (h x) (h y)) f y = fourB μ B (fun v => f (h.symm v)) (h y) := by sorry
