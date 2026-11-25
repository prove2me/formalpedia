-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_hasDerivAt_expG_apply
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.hasDerivAt_expG_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:31:44.626794+00:00
-- url     : https://prove2.me/theorems/cc1c10f4-2257-446e-a751-b290e81bc125
-- title:
--   Is Exp Lie Algebra: has Deriv At exp G apply
-- statement:
--   The Is Exp Lie Algebra construction uses the has Deriv At exp G apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L212-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L212-L249

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Garding
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.hasDerivAt_expG_apply (hπ : ∀ g, ‖π g‖ ≤ 1) {w : ℝ → E} {w' : E}
    (hw : HasDerivAt w w' 0) (hw0 : h.IsSmoothVector π (w 0)) (X : 𝔤) :
    HasDerivAt (fun t : ℝ => π (h.expG (t • X)) (w t)) (h.derivOp π X (w 0) + w') 0 := by sorry
