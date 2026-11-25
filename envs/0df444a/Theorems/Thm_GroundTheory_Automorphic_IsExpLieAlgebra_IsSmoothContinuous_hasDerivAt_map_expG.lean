-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_IsSmoothContinuous_hasDerivAt_map_expG
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.IsSmoothContinuous.hasDerivAt_map_expG
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:03:10.217438+00:00
-- url     : https://prove2.me/theorems/2b26eaee-323c-48b1-8a3c-3b883a678226
-- title:
--   Is Smooth Continuous: has Deriv At map exp G
-- statement:
--   The Is Smooth Continuous construction uses the has Deriv At map exp G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/Frechet.lean#L118-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/Frechet.lean#L118-L125

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.IsSmoothContinuous.hasDerivAt_map_expG (hπ : ∀ g, ‖π g‖ ≤ 1)
    {l : h.smoothVectors π →ₗ[ℂ] ℂ} (hl : h.IsSmoothContinuous π l) {v : E}
    (hv : h.IsSmoothVector π v) (g : G) (X : 𝔤) :
    HasDerivAt (fun t : ℝ => l (h.smoothMap π hv (g * h.expG (t • X))))
      (l (h.smoothMap π (h.isSmoothVector_derivOp π hv X) g)) 0 := by sorry
