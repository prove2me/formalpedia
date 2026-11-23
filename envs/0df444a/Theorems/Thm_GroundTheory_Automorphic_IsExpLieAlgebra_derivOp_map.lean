-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivOp_map
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.derivOp_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:56.186466+00:00
-- url     : https://prove2.me/theorems/0dbe3fec-9628-42d6-90a0-c158507a8f48
-- title:
--   Is Exp Lie Algebra: deriv Op map
-- statement:
--   The Is Exp Lie Algebra construction uses the deriv Op map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/SmoothVectors.lean#L221-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/SmoothVectors.lean#L221-L232

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.derivOp_map {v : E} (hv : h.IsSmoothVector π v) (g : G) (X : 𝔤) :
    h.derivOp π (h.Ad g X) (π g v) = π g (h.derivOp π X v) := by sorry
