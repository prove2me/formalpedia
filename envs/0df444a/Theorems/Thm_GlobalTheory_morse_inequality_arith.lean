-- Prove2me | Theorems.Thm_GlobalTheory_morse_inequality_arith
-- name    : GlobalTheory.morse_inequality_arith
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:10.356332+00:00
-- url     : https://prove2.me/theorems/3ac952ce-83f0-54a9-960d-5736fbfc20a4
-- title:
--   Global Theory: morse inequality arith
-- statement:
--   The Global Theory construction uses the morse inequality arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MorseInequalityArith.lean#L5-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MorseInequalityArith.lean#L5-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MorseInequalityArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.morse_inequality_arith (d : ℕ) (a b : ℤ) (h g : ℕ → ℕ) (C C' m₀ m₁ : ℕ)
    (H1 : ∀ m : ℕ, m₀ ≤ m → |((d + 1).factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ (d + 1)| ≤
      C * (((d + 1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ (d + 1 - 1)))
    (H2 : ∀ m : ℕ, m₁ ≤ m → |(d.factorial : ℤ) * (g m : ℤ) - b * (m : ℤ) ^ d| ≤
      C' * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)))
    (hab : ((d : ℤ) + 1) * b < a) : ∃ m : ℕ, 1 ≤ m ∧ m * g m < h m := by sorry
