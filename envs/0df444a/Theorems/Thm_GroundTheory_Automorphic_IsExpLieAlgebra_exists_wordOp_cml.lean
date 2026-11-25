-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_exists_wordOp_cml
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.exists_wordOp_cml
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:32:23.397423+00:00
-- url     : https://prove2.me/theorems/d44be540-68ee-46c4-8d37-cad2f079422b
-- title:
--   Is Exp Lie Algebra: exists word Op cml
-- statement:
--   The Is Exp Lie Algebra construction uses the exists word Op cml property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L136-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L136-L142

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.exists_wordOp_cml {v : E} (hv : h.IsSmoothVector π v) (k : ℕ) :
    ∃ Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => 𝔤) E, ∀ Y, Φ Y = h.wordOp π Y v := by sorry
