-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:48.96185+00:00
-- url     : https://prove2.me/theorems/52ca5702-96d3-4e5d-bad2-dd162f599d88
-- title:
--   Is Exp Lie Algebra: coe right Translate End
-- statement:
--   The Is Exp Lie Algebra construction uses the coe right Translate End property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/RightRegular.lean#L214-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/RightRegular.lean#L214-L215

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
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
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd (a : G) (f : h.smoothFuns (F := F)) :
    ((h.rightTranslateEnd a f : h.smoothFuns (F := F)) : G → F) = rightTranslate a f := by sorry

attribute [defeq] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
