-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_rightDeriv_mem_of_isKStable
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.rightDeriv_mem_of_isKStable
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:31.336259+00:00
-- url     : https://prove2.me/theorems/3d13d06f-df64-4dd2-9ab9-5fa69cb5dbfc
-- title:
--   Is Exp Lie Algebra: right Deriv mem of is KStable
-- statement:
--   The Is Exp Lie Algebra construction uses the right Deriv mem of is KStable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ZKFinite.lean#L250-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ZKFinite.lean#L250-L272

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
variable (K : Subgroup G)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.rightDeriv_mem_of_isKStable {V : Submodule ℂ (h.smoothFuns (F := F))}
    [FiniteDimensional ℂ V] (hV : ∀ (k : K), ∀ w ∈ V, h.rightTranslateEnd (k : G) w ∈ V)
    {X : 𝔤} (hX : ∀ t : ℝ, h.expG (t • X) ∈ K) {w : h.smoothFuns (F := F)} (hw : w ∈ V) :
    h.rightDerivEnd X w ∈ V := by sorry
