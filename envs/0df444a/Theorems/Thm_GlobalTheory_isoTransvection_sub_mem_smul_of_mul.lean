-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_sub_mem_smul_of_mul
-- name    : GlobalTheory.isoTransvection.sub_mem_smul_of_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:01:36.26153+00:00
-- url     : https://prove2.me/theorems/935cb1ab-c7c0-4b9d-81fb-359ca7f7c7e7
-- title:
--   iso Transvection: sub mem smul of mul
-- statement:
--   The iso Transvection construction uses the sub mem smul of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L193-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L193-L198

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

theorem GlobalTheory.isoTransvection.sub_mem_smul_of_mul {L : Submodule R₀ M} (hxL : x ∈ L) {I : Ideal R₀} {b : R} {v : M}
    (hb : ∃ c ∈ I, algebraMap R₀ R c = b * h v x) :
    isoTransvection h x hx b v - v ∈ I • L := by sorry
