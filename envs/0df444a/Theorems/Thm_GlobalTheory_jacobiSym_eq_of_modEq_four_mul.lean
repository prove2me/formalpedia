-- Prove2me | Theorems.Thm_GlobalTheory_jacobiSym_eq_of_modEq_four_mul
-- name    : GlobalTheory.jacobiSym_eq_of_modEq_four_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:02:42.320801+00:00
-- url     : https://prove2.me/theorems/2a12f5f9-3b4b-48ed-9f11-cdf785562ae1
-- title:
--   Global Theory: jacobi Sym eq of mod Eq four mul
-- statement:
--   The Global Theory construction uses the jacobi Sym eq of mod Eq four mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JacobiSymEqOfModEqFourMul.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JacobiSymEqOfModEqFourMul.lean#L6-L10

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JacobiSymEqOfModEqFourMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.jacobiSym_eq_of_modEq_four_mul (a q q' : ℕ) (hq : Odd q) (hq' : Odd q')
    (h : q ≡ q' [MOD 4 * a]) : jacobiSym (a : ℤ) q = jacobiSym (a : ℤ) q' := by sorry
