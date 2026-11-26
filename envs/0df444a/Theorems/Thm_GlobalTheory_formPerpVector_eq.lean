-- Prove2me | Theorems.Thm_GlobalTheory_formPerpVector_eq
-- name    : GlobalTheory.formPerpVector_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:47.759349+00:00
-- url     : https://prove2.me/theorems/8a148bfb-7259-50e5-b566-f6b3b6644734
-- title:
--   Global Theory: form Perp Vector eq
-- statement:
--   The Global Theory construction uses the form Perp Vector eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L241-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L241-L243

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

theorem GlobalTheory.formPerpVector_eq (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) (g : M) :
    formPerpVector h e e' g = (formPairMatrix h e e').det • g
      - ∑ a, ∑ a', ((formPairMatrix h e e').adjugate a a' * h g (e a)) • e' a' := by sorry
