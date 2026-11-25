-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_IsSmoothContinuous_exists_norm_map_le
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.IsSmoothContinuous.exists_norm_map_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:05:37.940803+00:00
-- url     : https://prove2.me/theorems/e5ef0328-3f5b-41eb-810c-093561b793d8
-- title:
--   Is Smooth Continuous: exists norm map le
-- statement:
--   The Is Smooth Continuous construction uses the exists norm map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/Frechet.lean#L150-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/Frechet.lean#L150-L175

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
variable {h π}

theorem GroundTheory.Automorphic.IsExpLieAlgebra.IsSmoothContinuous.exists_norm_map_le (hπ : ∀ g, ‖π g‖ ≤ 1)
    {l : h.smoothVectors π →ₗ[ℂ] ℂ} (hl : h.IsSmoothContinuous π l) {v : E}
    (hv : h.IsSmoothVector π v) :
    ∃ C N, ∀ g : G, ‖l (h.smoothMap π hv g)‖ ≤ C * (1 + ‖h.AdL g⁻¹‖) ^ N := by sorry
