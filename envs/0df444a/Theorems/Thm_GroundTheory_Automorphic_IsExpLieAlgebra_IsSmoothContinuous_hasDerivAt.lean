-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_IsSmoothContinuous_hasDerivAt
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.IsSmoothContinuous.hasDerivAt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:03:07.588803+00:00
-- url     : https://prove2.me/theorems/237729ed-2150-4e24-bddc-d11de97b2760
-- title:
--   Is Smooth Continuous: has Deriv At
-- statement:
--   The Is Smooth Continuous construction uses the has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/Frechet.lean#L83-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/Frechet.lean#L83-L108

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

theorem GroundTheory.Automorphic.IsExpLieAlgebra.IsSmoothContinuous.hasDerivAt {l : h.smoothVectors π →ₗ[ℂ] ℂ}
    (hl : h.IsSmoothContinuous π l) {u : ℝ → h.smoothVectors π} {d : h.smoothVectors π}
    (hu : ∀ Y : (Σ k, Fin k → 𝔤),
      HasDerivAt (fun t => h.wordOp π Y.2 (u t : E)) (h.wordOp π Y.2 (d : E)) 0) :
    HasDerivAt (fun t => l (u t)) (l d) 0 := by sorry
