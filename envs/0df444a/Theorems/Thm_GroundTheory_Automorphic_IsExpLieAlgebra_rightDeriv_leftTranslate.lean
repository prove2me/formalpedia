-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_rightDeriv_leftTranslate
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.rightDeriv_leftTranslate
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:34:58.410669+00:00
-- url     : https://prove2.me/theorems/29fb8ae6-3351-497c-af15-b77053a1da5e
-- title:
--   Is Exp Lie Algebra: right Deriv left Translate
-- statement:
--   The Is Exp Lie Algebra construction uses the right Deriv left Translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AutomorphicFormSpaces/LeftTranslate.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AutomorphicFormSpaces/LeftTranslate.lean#L33-L36

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.rightDeriv_leftTranslate (X : 𝔤) (f : G → F) (a : G) :
    h.rightDeriv X (leftTranslate a f) = leftTranslate a (h.rightDeriv X f) := by sorry
