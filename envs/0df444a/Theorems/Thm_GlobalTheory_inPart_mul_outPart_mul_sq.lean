-- Prove2me | Theorems.Thm_GlobalTheory_inPart_mul_outPart_mul_sq
-- name    : GlobalTheory.inPart_mul_outPart_mul_sq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:54:51.07847+00:00
-- url     : https://prove2.me/theorems/39679573-117f-498b-95e4-fa6d9d7d6a64
-- title:
--   Global Theory: in Part mul out Part mul sq
-- statement:
--   The Global Theory construction uses the in Part mul out Part mul sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/InPartMulOutPartMulSq.lean#L10-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/InPartMulOutPartMulSq.lean#L10-L33

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_InPartMulOutPartMulSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2

theorem GlobalTheory.inPart_mul_outPart_mul_sq (m₀ m : ℕ) (hm : 0 < m) :
    inPart m₀ m * outPart m₀ m * (∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2)) ^ 2 = m := by sorry
