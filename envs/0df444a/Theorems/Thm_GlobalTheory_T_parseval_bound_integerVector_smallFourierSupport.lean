-- Prove2me | Theorems.Thm_GlobalTheory_T_parseval_bound_integerVector_smallFourierSupport
-- name    : GlobalTheory.T.parseval_bound_integerVector_smallFourierSupport
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:55:14.779253+00:00
-- url     : https://prove2.me/theorems/f0c189bd-1fac-4f5a-ba8d-86f866c57aea
-- title:
--   T: parseval bound integer Vector small Fourier Support
-- statement:
--   The T construction uses the parseval bound integer Vector small Fourier Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParsevalBoundIntegerVectorSmallFourierSupportStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ParsevalBoundIntegerVectorSmallFourierSupportStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParsevalBoundIntegerVectorSmallFourierSupport
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ParsevalBoundIntegerVectorSmallFourierSupportStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.parseval_bound_integerVector_smallFourierSupport : ∀ (n N : ℕ) (ω : ℂ) (c : ℕ → ℤ) (S : Finset ℕ), 0 < n → 0 < N → IsPrimitiveRoot ω N → ∑ k ∈ Finset.range N, c k ^ 2 = 2 * n → |∑ k ∈ Finset.range N, c k| ≤ (n : ℤ) - 1 → (∀ j : ℕ, 0 < j → j < N → j ∉ S → ∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) = 0) → 2 * n * N ≤ (n - 1) ^ 2 + 4 * n ^ 2 * S.card := by sorry
