-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_expChart_GL_mem_maximalAtlas
-- name    : GroundTheory.Automorphic.expChart_GL_mem_maximalAtlas
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:43.435791+00:00
-- url     : https://prove2.me/theorems/3b90b8cc-13a9-588e-89c4-42a2423bea6c
-- title:
--   Automorphic: exp Chart GL mem maximal Atlas
-- statement:
--   The Automorphic construction uses the exp Chart GL mem maximal Atlas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsLie.lean#L180-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsLie.lean#L180-L183

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set
set_option linter.unusedSectionVars false
open scoped Matrix.Norms.L2Operator

theorem GroundTheory.Automorphic.expChart_GL_mem_maximalAtlas (𝕂 : Type*) [RCLike 𝕂] (n : ℕ) (g : GL (Fin n) 𝕂)
    (k : WithTop ℕ∞) :
    expChartUnits 𝕂 g ∈ IsManifold.maximalAtlas 𝓘(𝕂, Matrix (Fin n) (Fin n) 𝕂) k (GL (Fin n) 𝕂) := by sorry
