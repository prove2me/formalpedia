-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_bracket
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.Ad_bracket
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:37.140158+00:00
-- url     : https://prove2.me/theorems/d36146c9-8fd5-46f3-8ed6-e4892f8fc498
-- title:
--   Is Exp Lie Algebra: Ad bracket
-- statement:
--   The Is Exp Lie Algebra construction uses the Ad bracket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/LieAlgebra.lean#L97-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/LieAlgebra.lean#L97-L109

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_LieAlgebra
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
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
include h

theorem GroundTheory.Automorphic.IsExpLieAlgebra.Ad_bracket (g : G) (X Y : 𝔤) :
    h.Ad g (h.bracket X Y) = h.bracket (h.Ad g X) (h.Ad g Y) := by sorry
