-- Prove2me | Theorems.Thm_GlobalTheory_formPairMatrix_apply
-- name    : GlobalTheory.formPairMatrix_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:07.376525+00:00
-- url     : https://prove2.me/theorems/ef601069-cec7-4f3a-a489-c961a9ecae44
-- title:
--   Global Theory: form Pair Matrix apply
-- statement:
--   The Global Theory construction uses the form Pair Matrix apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L238-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L238-L239

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
omit [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.formPairMatrix_apply (h : M →ₗ[R] M →ₛₗ[σ] R) (e e' : ι → M) (a' a : ι) :
    formPairMatrix h e e' a' a = h (e' a') (e a) := by sorry

attribute [defeq] GlobalTheory.formPairMatrix_apply
