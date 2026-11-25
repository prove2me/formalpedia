-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_lieGroup_GL_complex_real
-- name    : GroundTheory.Automorphic.lieGroup_GL_complex_real
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:40.011042+00:00
-- url     : https://prove2.me/theorems/308490ca-b5ff-4dad-9f5c-6e01930188e3
-- title:
--   Automorphic: lie Group GL complex real
-- statement:
--   The Automorphic construction uses the lie Group GL complex real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsLie.lean#L177-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsLie.lean#L177-L178

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

theorem GroundTheory.Automorphic.lieGroup_GL_complex_real (n : ℕ) (k : WithTop ℕ∞) :
    LieGroup 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) k (GL (Fin n) ℂ) := by sorry
