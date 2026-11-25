-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_continuous_wordOp_map
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.continuous_wordOp_map
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:48.694924+00:00
-- url     : https://prove2.me/theorems/8617a2b9-a8cc-45cb-b09b-8e84fa1a8e62
-- title:
--   Is Exp Lie Algebra: continuous word Op map
-- statement:
--   The Is Exp Lie Algebra construction uses the continuous word Op map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L347-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L347-L355

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.continuous_wordOp_map (hπ : ∀ g, ‖π g‖ ≤ 1) {v : E} (hv : h.IsSmoothVector π v)
    {k : ℕ} (Y : Fin k → 𝔤) : Continuous fun g : G => h.wordOp π Y (π g v) := by sorry
