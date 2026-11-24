-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ParamIntegral_fderiv_iter
-- name    : GroundTheory.Automorphic.ParamIntegral.fderiv_iter
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:56.612138+00:00
-- url     : https://prove2.me/theorems/9a26f22a-cd86-471f-bc8d-3c2ed11f2dd0
-- title:
--   Param Integral: fderiv iter
-- statement:
--   The Param Integral construction uses the fderiv iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ParametricIntegral.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ParametricIntegral.lean#L28-L31

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
open GroundTheory.Automorphic.ParamIntegral
variable (F : P → α → F')
variable {F}

theorem GroundTheory.Automorphic.ParamIntegral.fderiv_iter (k : ℕ) (Y : P) (a : α) :
    fderiv ℝ (fun Y => iter F k Y a) Y =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => P) F' (iter F (k + 1) Y a) := by sorry
