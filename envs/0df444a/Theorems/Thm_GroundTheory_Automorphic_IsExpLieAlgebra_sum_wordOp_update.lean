-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_sum_wordOp_update
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.sum_wordOp_update
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:41:52.542779+00:00
-- url     : https://prove2.me/theorems/fdeb8f3d-58c4-4bdf-b002-10db910718c9
-- title:
--   Is Exp Lie Algebra: sum word Op update
-- statement:
--   The Is Exp Lie Algebra construction uses the sum word Op update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L194-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/ContinuousMultilinearOfFiniteDimensional.lean#L194-L210

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.sum_wordOp_update {v : E} (hv : h.IsSmoothVector π v) (X : 𝔤) :
    ∀ {k : ℕ} (Y : Fin k → 𝔤),
      ∑ i, h.wordOp π (Function.update Y i (h.bracket X (Y i))) v = h.brSum π X Y v
  := by sorry
