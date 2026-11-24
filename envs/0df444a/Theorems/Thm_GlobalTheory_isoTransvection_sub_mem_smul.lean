-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_sub_mem_smul
-- name    : GlobalTheory.isoTransvection.sub_mem_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:01:32.263881+00:00
-- url     : https://prove2.me/theorems/3b81a15a-c815-42d9-a241-dc99a2740e60
-- title:
--   iso Transvection: sub mem smul
-- statement:
--   The iso Transvection construction uses the sub mem smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L200-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L200-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.isoTransvection
variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)
variable {h}
variable (h)
variable {R₀ : Type*} [CommRing R₀] [Algebra R₀ R] [Module R₀ M] [IsScalarTower R₀ R M]

theorem GlobalTheory.isoTransvection.sub_mem_smul {L : Submodule R₀ M} (hxL : x ∈ L)
    (hL : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range) {I : Ideal R₀} {b : R₀} (hb : b ∈ I)
    {v : M} (hv : v ∈ L) :
    isoTransvection h x hx (algebraMap R₀ R b) v - v ∈ I • L := by sorry
