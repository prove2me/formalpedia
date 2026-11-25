-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_rightDerivEnd_mul_leftTranslateEnd
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.rightDerivEnd_mul_leftTranslateEnd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:39:49.530823+00:00
-- url     : https://prove2.me/theorems/36ace509-a182-4d26-ad8d-36adf18510ab
-- title:
--   Is Exp Lie Algebra: right Deriv End mul left Translate End
-- statement:
--   The Is Exp Lie Algebra construction uses the right Deriv End mul left Translate End property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AutomorphicFormSpaces/LeftTranslate.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AutomorphicFormSpaces/LeftTranslate.lean#L61-L63

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_AutomorphicFormSpaces_LeftTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem GroundTheory.Automorphic.IsExpLieAlgebra.rightDerivEnd_mul_leftTranslateEnd (X : 𝔤) (a : G) :
    h.rightDerivEnd (F := F) X * h.leftTranslateEnd a = h.leftTranslateEnd a * h.rightDerivEnd X := by sorry
