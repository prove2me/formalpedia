-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_iteratedFDeriv_integral_eq
-- name    : GroundTheory.Automorphic.iteratedFDeriv_integral_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:58.656254+00:00
-- url     : https://prove2.me/theorems/6a04760c-a94c-4234-bdbf-46541a456dce
-- title:
--   Automorphic: iterated FDeriv integral eq
-- statement:
--   The Automorphic construction uses the iterated FDeriv integral eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ParametricIntegral.lean#L82-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ParametricIntegral.lean#L82-L106

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Metric
open scoped ContDiff
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable {α : Type*} [TopologicalSpace α] [T2Space α] [SecondCountableTopology α]
  [MeasurableSpace α] [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F']
open ParamIntegral

theorem GroundTheory.Automorphic.iteratedFDeriv_integral_eq (F : P → α → F')
    (hF : ∀ a, ContDiff ℝ ∞ (fun Y => F Y a))
    (hcont : ∀ k : ℕ, Continuous (fun p : P × α => iter F k p.1 p.2))
    (hsupp : ∀ Y₀ : P, ∃ U ∈ 𝓝 Y₀, ∃ C : Set α, IsCompact C ∧ ∀ Y ∈ U, ∀ a ∉ C, F Y a = 0)
    (k : ℕ) :
    iteratedFDeriv ℝ k (fun Y => ∫ a, F Y a ∂μ) = fun Y => ∫ a, iter F k Y a ∂μ := by sorry
