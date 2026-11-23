-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expG_Ad
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.expG_Ad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:29.235182+00:00
-- url     : https://prove2.me/theorems/ca0cef33-fe6b-4a33-9e17-00326ea32d6f
-- title:
--   Is Exp Lie Algebra: exp G Ad
-- statement:
--   The Is Exp Lie Algebra construction uses the exp G Ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/LieAlgebra.lean#L115-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/LieAlgebra.lean#L115-L118

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.expG_Ad (g : G) (X : 𝔤) : h.expG (h.Ad g X) = g * h.expG X * g⁻¹ := by sorry
