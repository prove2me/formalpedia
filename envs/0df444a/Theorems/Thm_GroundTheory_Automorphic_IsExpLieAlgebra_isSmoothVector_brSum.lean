-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isSmoothVector_brSum
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.isSmoothVector_brSum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:21.164505+00:00
-- url     : https://prove2.me/theorems/c98dc6d4-8a21-4e1a-b382-8478ddbb63d4
-- title:
--   Is Exp Lie Algebra: is Smooth Vector br Sum
-- statement:
--   The Is Exp Lie Algebra construction uses the is Smooth Vector br Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L164-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L164-L169

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.isSmoothVector_brSum {v : E} (hv : h.IsSmoothVector π v) (X : 𝔤) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤), h.IsSmoothVector π (h.brSum π X Y v)
  := by sorry
