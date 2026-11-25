-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_lieGroup_GL
-- name    : GroundTheory.Automorphic.lieGroup_GL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:49.293215+00:00
-- url     : https://prove2.me/theorems/68dd6bce-dc8b-4aa7-9a3f-7e17ddd92913
-- title:
--   Automorphic: lie Group GL
-- statement:
--   The Automorphic construction uses the lie Group GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsLie.lean#L174-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsLie.lean#L174-L175

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

theorem GroundTheory.Automorphic.lieGroup_GL (𝕂 : Type*) [RCLike 𝕂] (n : ℕ) (k : WithTop ℕ∞) :
    LieGroup 𝓘(𝕂, Matrix (Fin n) (Fin n) 𝕂) k (GL (Fin n) 𝕂) := by sorry
