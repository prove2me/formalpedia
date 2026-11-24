-- Prove2me | Theorems.Thm_GlobalTheory_div_mem_of_mul_pow_div_mem_of_regularPair
-- name    : GlobalTheory.div_mem_of_mul_pow_div_mem_of_regularPair
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:16:37.427364+00:00
-- url     : https://prove2.me/theorems/5bd6f37a-9484-4693-9752-b9c3d9651017
-- title:
--   Global Theory: div mem of mul pow div mem of regular Pair
-- statement:
--   The Global Theory construction uses the div mem of mul pow div mem of regular Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DivMemOfMulPowDivMemOfRegularPair.lean#L5-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DivMemOfMulPowDivMemOfRegularPair.lean#L5-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivMemOfMulPowDivMemOfRegularPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.div_mem_of_mul_pow_div_mem_of_regularPair (K : Type) [Field K] (O : Subring K) (s t : K)
    (ht : t ∈ O) (h : ∀ g ∈ O, g * t / s ∈ O → g / s ∈ O) (N : ℕ) :
    ∀ g ∈ O, g * t ^ N / s ∈ O → g / s ∈ O := by sorry
