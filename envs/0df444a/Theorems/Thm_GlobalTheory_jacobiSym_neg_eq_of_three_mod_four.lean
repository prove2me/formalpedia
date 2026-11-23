-- Prove2me | Theorems.Thm_GlobalTheory_jacobiSym_neg_eq_of_three_mod_four
-- name    : GlobalTheory.jacobiSym_neg_eq_of_three_mod_four
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:26.492949+00:00
-- url     : https://prove2.me/theorems/5cee7a97-5b26-4bfc-ae42-8c2a64bca414
-- title:
--   Global Theory: jacobi Sym neg eq of three mod four
-- statement:
--   The Global Theory construction uses the jacobi Sym neg eq of three mod four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JacobiSymNegEqOfThreeModFour.lean#L6-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/JacobiSymNegEqOfThreeModFour.lean#L6-L17

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JacobiSymNegEqOfThreeModFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.jacobiSym_neg_eq_of_three_mod_four (q n : ℕ) (hq : q % 4 = 3) (hn : Odd n) :
    jacobiSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q := by sorry
