-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:22.147499+00:00
-- url     : https://prove2.me/theorems/b4f844df-f478-40bf-96fa-639930c6c62a
-- title:
--   Is Exp Lie Algebra: deriv Lie apply
-- statement:
--   The Is Exp Lie Algebra construction uses the deriv Lie apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/SmoothVectors.lean#L379-L380
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/SmoothVectors.lean#L379-L380

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
attribute [local instance 100] LieRing.ofAssociativeRing

theorem GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply (X : h.lieSubalgebra) : h.derivLie π X = h.derivEnd π (h.ofLie X) := by sorry

attribute [defeq] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
