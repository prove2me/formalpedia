-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expOrbit_apply
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.expOrbit_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:38.966182+00:00
-- url     : https://prove2.me/theorems/32569116-d3d9-40b5-91fb-65a5fb57982e
-- title:
--   Is Exp Lie Algebra: exp Orbit apply
-- statement:
--   The Is Exp Lie Algebra construction uses the exp Orbit apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/SmoothVectors.lean#L130-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/SmoothVectors.lean#L130-L130

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_LieAlgebra
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_IsInvariantIffCommuteStarProjection
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.expOrbit_apply (v : E) (Y : 𝔤) : h.expOrbit π v Y = π (h.expG Y) v := by sorry
