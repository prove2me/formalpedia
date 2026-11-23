-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_hasDerivAt_Ad_expG
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.hasDerivAt_Ad_expG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:44.746315+00:00
-- url     : https://prove2.me/theorems/faaf5561-900b-48a3-8587-d2236a48bad8
-- title:
--   Is Exp Lie Algebra: has Deriv At Ad exp G
-- statement:
--   The Is Exp Lie Algebra construction uses the has Deriv At Ad exp G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/LieAlgebra.lean#L120-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/LieAlgebra.lean#L120-L139

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.hasDerivAt_Ad_expG (X Y : 𝔤) :
    HasDerivAt (fun t : ℝ => h.Ad (h.expG (t • X)) Y) (h.bracket X Y) 0 := by sorry
