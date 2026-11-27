-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_mem_gkVectors
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.mem_gkVectors
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:21.618853+00:00
-- url     : https://prove2.me/theorems/2b88b183-354a-58f2-a586-83632dac9193
-- title:
--   Is Exp Lie Algebra: mem gk Vectors
-- statement:
--   The Is Exp Lie Algebra construction uses the mem gk Vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/GKModule.lean#L208-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/GKModule.lean#L208-L209

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
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
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E) (K : Subgroup G)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.mem_gkVectors {v : E} :
    v ∈ h.gkVectors π K ↔ h.IsSmoothVector π v ∧ π.IsKFinite K v := by sorry
