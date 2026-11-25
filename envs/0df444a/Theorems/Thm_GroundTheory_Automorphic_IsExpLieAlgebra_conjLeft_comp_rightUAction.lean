-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_conjLeft_comp_rightUAction
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.conjLeft_comp_rightUAction
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:41:05.590411+00:00
-- url     : https://prove2.me/theorems/b00af25f-04d5-4882-a6e2-0a6967c6c36d
-- title:
--   Is Exp Lie Algebra: conj Left comp right UAction
-- statement:
--   The Is Exp Lie Algebra construction uses the conj Left comp right UAction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AutomorphicFormSpaces/LeftTranslate.lean#L80-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AutomorphicFormSpaces/LeftTranslate.lean#L80-L89

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.conjLeft_comp_rightUAction (a : G) :
    (h.conjLeft (F := F) a).comp (h.rightUAction (F := F)) = h.rightUAction (F := F) := by sorry
