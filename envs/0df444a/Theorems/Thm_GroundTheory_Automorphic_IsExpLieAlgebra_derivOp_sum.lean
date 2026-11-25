-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivOp_sum
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.derivOp_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:03.883465+00:00
-- url     : https://prove2.me/theorems/8d210c81-a20b-4b54-bd28-0e0b54873f02
-- title:
--   Is Exp Lie Algebra: deriv Op sum
-- statement:
--   The Is Exp Lie Algebra construction uses the deriv Op sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L184-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L184-L192

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.derivOp_sum {ι : Type*} (s : Finset ι) {w : ι → E} (hw : ∀ i, h.IsSmoothVector π (w i))
    (X : 𝔤) : h.derivOp π X (∑ i ∈ s, w i) = ∑ i ∈ s, h.derivOp π X (w i) := by sorry
