-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hasFDerivAt_integral_iter
-- name    : GroundTheory.Automorphic.hasFDerivAt_integral_iter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:08.63792+00:00
-- url     : https://prove2.me/theorems/9b459f91-fdb3-4ebd-8f98-17cedc93505b
-- title:
--   Automorphic: has FDeriv At integral iter
-- statement:
--   The Automorphic construction uses the has FDeriv At integral iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ParametricIntegral.lean#L39-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ParametricIntegral.lean#L39-L80

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
set_option synthInstance.maxHeartbeats 200000

theorem GroundTheory.Automorphic.hasFDerivAt_integral_iter (F : P → α → F')
    (hF : ∀ a, ContDiff ℝ ∞ (fun Y => F Y a))
    (hcont : ∀ k : ℕ, Continuous (fun p : P × α => iter F k p.1 p.2))
    (hsupp : ∀ Y₀ : P, ∃ U ∈ 𝓝 Y₀, ∃ C : Set α, IsCompact C ∧ ∀ Y ∈ U, ∀ a ∉ C, F Y a = 0)
    (k : ℕ) (Y₀ : P) :
    HasFDerivAt (fun Y => ∫ a, iter F k Y a ∂μ)
      (∫ a, continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => P) F'
        (iter F (k + 1) Y₀ a) ∂μ) Y₀ := by sorry
