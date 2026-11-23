-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:06.389946+00:00
-- url     : https://prove2.me/theorems/61e27282-c6d8-46ce-859d-4b0088f10f0c
-- title:
--   Is Exp Lie Algebra: coe Ad
-- statement:
--   The Is Exp Lie Algebra construction uses the coe Ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/LieAlgebra.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/LieAlgebra.lean#L80-L81

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad (g : G) (X : 𝔤) :
    ((h.Ad g X : 𝔤) : 𝔸) = ((g : 𝔸ˣ) : 𝔸) * X * (((g⁻¹ : G) : 𝔸ˣ) : 𝔸) := by sorry

attribute [defeq] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
