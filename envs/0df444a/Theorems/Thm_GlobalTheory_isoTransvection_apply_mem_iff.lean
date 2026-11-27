-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_apply_mem_iff
-- name    : GlobalTheory.isoTransvection.apply_mem_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:18.404626+00:00
-- url     : https://prove2.me/theorems/760a80b5-c0b9-5e2f-ba4e-acf1d8301d9c
-- title:
--   iso Transvection: apply mem iff
-- statement:
--   The iso Transvection construction uses the apply mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L221-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L221-L226

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

theorem GlobalTheory.isoTransvection.apply_mem_iff {L : Submodule R₀ M} (hxL : x ∈ L)
    (hL : ∀ v ∈ L, h v x ∈ (algebraMap R₀ R).range) (b : R₀) (v : M) :
    isoTransvection h x hx (algebraMap R₀ R b) v ∈ L ↔ v ∈ L := by sorry
