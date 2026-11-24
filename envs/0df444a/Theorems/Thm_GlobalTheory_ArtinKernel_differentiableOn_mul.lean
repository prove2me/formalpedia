-- Prove2me | Theorems.Thm_GlobalTheory_ArtinKernel_differentiableOn_mul
-- name    : GlobalTheory.ArtinKernel.differentiableOn_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:58:44.783568+00:00
-- url     : https://prove2.me/theorems/bb60e206-9e4f-4c69-b0a1-5f76149cbd74
-- title:
--   Artin Kernel: differentiable On mul
-- statement:
--   The Artin Kernel construction uses the differentiable On mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLinearOfMulPeriod.lean#L158-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsLinearOfMulPeriod.lean#L158-L172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.ArtinKernel
variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]
omit [IsLocalRing R]

theorem GlobalTheory.ArtinKernel.differentiableOn_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E} {F G : E → R}
    (hF : ∀ lam : R →ₗ[ℂ] ℂ, DifferentiableOn ℂ (fun z => lam (F z)) S)
    (hG : ∀ lam : R →ₗ[ℂ] ℂ, DifferentiableOn ℂ (fun z => lam (G z)) S) (lam : R →ₗ[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z => lam (F z * G z)) S := by sorry
