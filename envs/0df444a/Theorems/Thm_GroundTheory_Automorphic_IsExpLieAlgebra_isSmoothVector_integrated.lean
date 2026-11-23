-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isSmoothVector_integrated
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.isSmoothVector_integrated
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:57.317247+00:00
-- url     : https://prove2.me/theorems/f9a00d58-8501-4345-a30f-b01d580e43ca
-- title:
--   Is Exp Lie Algebra: is Smooth Vector integrated
-- statement:
--   The Is Exp Lie Algebra construction uses the is Smooth Vector integrated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/Garding.lean#L96-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/Garding.lean#L96-L152

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory NormedSpace Set Filter Topology Metric
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (π : BanachRep G E)
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ]

theorem GroundTheory.Automorphic.IsExpLieAlgebra.isSmoothVector_integrated {f : G → ℂ} (hf : h.IsTestFunction f) (v : E) :
    h.IsSmoothVector π (π.integrated μ f v) := by sorry
