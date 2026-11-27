-- Prove2me | Theorems.Thm_GlobalTheory_formPerpVector_mem_of_integral
-- name    : GlobalTheory.formPerpVector_mem_of_integral
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:05.036222+00:00
-- url     : https://prove2.me/theorems/4d6fc0b9-2c1e-48c7-ab9d-3c84de35a64a
-- title:
--   Global Theory: form Perp Vector mem of integral
-- statement:
--   The Global Theory construction uses the form Perp Vector mem of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L260-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L260-L265

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
  {σ : R →+* R}

theorem GlobalTheory.formPerpVector_mem_of_integral {A : Type*} [CommRing A] [Algebra A R] [Module A M]
    [IsScalarTower A R M] (L : Submodule A M) (h : M →ₗ[R] M →ₛₗ[σ] R)
    (hL : ∀ u ∈ L, ∀ v ∈ L, h u v ∈ (algebraMap A R).range) {e e' : ι → M} {g : M}
    (he : ∀ a, e a ∈ L) (he' : ∀ a, e' a ∈ L) (hg : g ∈ L) : formPerpVector h e e' g ∈ L := by sorry
