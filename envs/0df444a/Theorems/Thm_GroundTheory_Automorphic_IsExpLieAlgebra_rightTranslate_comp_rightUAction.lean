-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_rightTranslate_comp_rightUAction
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.rightTranslate_comp_rightUAction
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:21.857808+00:00
-- url     : https://prove2.me/theorems/881f5784-33c3-4fdd-8e4e-9ba7141cd5a7
-- title:
--   Is Exp Lie Algebra: right Translate comp right UAction
-- statement:
--   The Is Exp Lie Algebra construction uses the right Translate comp right UAction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ZKFinite.lean#L139-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ZKFinite.lean#L139-L142

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.rightTranslate_comp_rightUAction (a : G) (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    h.rightTranslateEnd (F := F) a * h.rightUAction u =
      h.rightUAction (h.AdU a u) * h.rightTranslateEnd a := by sorry
