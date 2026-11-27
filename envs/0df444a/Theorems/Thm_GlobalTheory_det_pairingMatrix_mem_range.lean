-- Prove2me | Theorems.Thm_GlobalTheory_det_pairingMatrix_mem_range
-- name    : GlobalTheory.det_pairingMatrix_mem_range
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:59.513436+00:00
-- url     : https://prove2.me/theorems/93ab2a9c-86f1-48ff-a144-5f47f0d6fa41
-- title:
--   Global Theory: det pairing Matrix mem range
-- statement:
--   The Global Theory construction uses the det pairing Matrix mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L53-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L53-L59

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
variable {A : Type*} [CommRing A] [Algebra A R]

theorem GlobalTheory.det_pairingMatrix_mem_range (ε : ι → Module.Dual R M) (e' : ι → M)
    (he : ∀ a a', ε a (e' a') ∈ (algebraMap A R).range) :
    (pairingMatrix ε e').det ∈ (algebraMap A R).range := by sorry
