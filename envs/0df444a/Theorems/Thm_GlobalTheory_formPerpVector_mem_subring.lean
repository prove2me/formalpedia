-- Prove2me | Theorems.Thm_GlobalTheory_formPerpVector_mem_subring
-- name    : GlobalTheory.formPerpVector_mem_subring
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:51:52.803901+00:00
-- url     : https://prove2.me/theorems/73de4046-58dc-49f6-89f4-b76470482a82
-- title:
--   Global Theory: form Perp Vector mem subring
-- statement:
--   The Global Theory construction uses the form Perp Vector mem subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L267-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L267-L271

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

theorem GlobalTheory.formPerpVector_mem_subring (A : Subring R) (L : Submodule A M)
    (h : M →ₗ[R] M →ₛₗ[σ] R) (e : ι → M) {e' : ι → M} {g : M} (he' : ∀ a, e' a ∈ L) (hgL : g ∈ L)
    (he : ∀ a a', h (e' a') (e a) ∈ A) (hg : ∀ a, h g (e a) ∈ A) :
    formPerpVector h e e' g ∈ L := by sorry
