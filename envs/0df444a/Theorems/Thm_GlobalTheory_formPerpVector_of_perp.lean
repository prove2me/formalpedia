-- Prove2me | Theorems.Thm_GlobalTheory_formPerpVector_of_perp
-- name    : GlobalTheory.formPerpVector_of_perp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:51:59.048398+00:00
-- url     : https://prove2.me/theorems/dbda1d11-e765-4e27-a742-15721867812c
-- title:
--   Global Theory: form Perp Vector of perp
-- statement:
--   The Global Theory construction uses the form Perp Vector of perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L249-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L249-L251

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

theorem GlobalTheory.formPerpVector_of_perp (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) {g : M}
    (hg : ∀ a, h g (e a) = 0) : formPerpVector h e e' g = (formPairMatrix h e e').det • g := by sorry
