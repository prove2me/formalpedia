-- Prove2me | Theorems.Thm_GlobalTheory_form_formPerpVector
-- name    : GlobalTheory.form_formPerpVector
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:52:58.806256+00:00
-- url     : https://prove2.me/theorems/96e3deb0-ea62-45e3-82f9-b36c3e7f6eef
-- title:
--   Global Theory: form form Perp Vector
-- statement:
--   The Global Theory construction uses the form form Perp Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L245-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L245-L247

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

theorem GlobalTheory.form_formPerpVector (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) (g : M) (c : ι) :
    h (formPerpVector h e e' g) (e c) = 0 := by sorry
