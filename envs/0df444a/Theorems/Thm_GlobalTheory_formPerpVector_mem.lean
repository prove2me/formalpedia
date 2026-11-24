-- Prove2me | Theorems.Thm_GlobalTheory_formPerpVector_mem
-- name    : GlobalTheory.formPerpVector_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:14.516497+00:00
-- url     : https://prove2.me/theorems/23a2a9a4-7772-476a-9f2f-f21cc9e32e5d
-- title:
--   Global Theory: form Perp Vector mem
-- statement:
--   The Global Theory construction uses the form Perp Vector mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L253-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L253-L258

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

theorem GlobalTheory.formPerpVector_mem {A : Type*} [CommRing A] [Algebra A R] [Module A M]
    [IsScalarTower A R M] (L : Submodule A M) (h : M →ₗ[R] M →ₛₗ[σ] R) (e : ι → M) {e' : ι → M}
    {g : M} (he' : ∀ a, e' a ∈ L) (hgL : g ∈ L)
    (he : ∀ a a', h (e' a') (e a) ∈ (algebraMap A R).range)
    (hg : ∀ a, h g (e a) ∈ (algebraMap A R).range) : formPerpVector h e e' g ∈ L := by sorry
