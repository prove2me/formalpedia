-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isSmoothVector_wordOp
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.isSmoothVector_wordOp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:31:20.251794+00:00
-- url     : https://prove2.me/theorems/8d9d52b7-7f9a-42c0-80c0-69da108c09b1
-- title:
--   Is Exp Lie Algebra: is Smooth Vector word Op
-- statement:
--   The Is Exp Lie Algebra construction uses the is Smooth Vector word Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L28-L31

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
open NormedSpace Set Filter Topology
open scoped ContDiff
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.isSmoothVector_wordOp {v : E} (hv : h.IsSmoothVector π v) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤), h.IsSmoothVector π (h.wordOp π Y v)
  := by sorry
