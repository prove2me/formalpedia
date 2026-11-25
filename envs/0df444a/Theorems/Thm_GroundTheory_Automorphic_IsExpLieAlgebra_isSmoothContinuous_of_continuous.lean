-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isSmoothContinuous_of_continuous
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.isSmoothContinuous_of_continuous
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:04:40.19041+00:00
-- url     : https://prove2.me/theorems/03734041-3933-45b5-83b3-26c55108c456
-- title:
--   Is Exp Lie Algebra: is Smooth Continuous of continuous
-- statement:
--   The Is Exp Lie Algebra construction uses the is Smooth Continuous of continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/Frechet.lean#L50-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/Frechet.lean#L50-L64

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_Frechet
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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.isSmoothContinuous_of_continuous (l : h.SmoothFrechet π →L[ℂ] ℂ) :
    h.IsSmoothContinuous π (l.toLinearMap : h.smoothVectors π →ₗ[ℂ] ℂ) := by sorry
