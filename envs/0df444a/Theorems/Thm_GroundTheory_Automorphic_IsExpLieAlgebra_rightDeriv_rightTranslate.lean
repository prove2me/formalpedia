-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_rightDeriv_rightTranslate
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.rightDeriv_rightTranslate
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:31:36.802611+00:00
-- url     : https://prove2.me/theorems/17d8555a-c50d-453c-8e40-ce6fa665f523
-- title:
--   Is Exp Lie Algebra: right Deriv right Translate
-- statement:
--   The Is Exp Lie Algebra construction uses the right Deriv right Translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/RightRegular.lean#L97-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/RightRegular.lean#L97-L112

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.rightDeriv_rightTranslate {f : G → F} (hf : h.IsSmoothFun f) (a : G) (X : 𝔤) :
    h.rightDeriv X (rightTranslate a f) = rightTranslate a (h.rightDeriv (h.Ad a⁻¹ X) f) := by sorry
