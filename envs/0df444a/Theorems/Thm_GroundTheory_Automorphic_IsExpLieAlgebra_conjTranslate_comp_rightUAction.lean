-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_conjTranslate_comp_rightUAction
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.conjTranslate_comp_rightUAction
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:14.659618+00:00
-- url     : https://prove2.me/theorems/c9bda5eb-ec0f-43dd-b694-70088dc77474
-- title:
--   Is Exp Lie Algebra: conj Translate comp right UAction
-- statement:
--   The Is Exp Lie Algebra construction uses the conj Translate comp right UAction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ZKFinite.lean#L113-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ZKFinite.lean#L113-L129

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ZKFinite
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
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem GroundTheory.Automorphic.IsExpLieAlgebra.conjTranslate_comp_rightUAction (a : G) :
    (h.conjTranslate (F := F) a).comp (h.rightUAction (F := F)) =
      (h.rightUAction (F := F)).comp (h.AdU a⁻¹) := by sorry
