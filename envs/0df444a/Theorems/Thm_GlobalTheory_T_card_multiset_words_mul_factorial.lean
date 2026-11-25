-- Prove2me | Theorems.Thm_GlobalTheory_T_card_multiset_words_mul_factorial
-- name    : GlobalTheory.T.card_multiset_words_mul_factorial
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:26:21.838693+00:00
-- url     : https://prove2.me/theorems/6935dee1-4a4a-5372-b8e1-2deea972e3ca
-- title:
--   T: card multiset words mul factorial
-- statement:
--   The T construction uses the card multiset words mul factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardMultisetWordsMulFactorialStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardMultisetWordsMulFactorialStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardMultisetWordsMulFactorial
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardMultisetWordsMulFactorialStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_multiset_words_mul_factorial : ∀ {I : Type} [Fintype I] (k : ℕ) (ν : I → ℕ), ∑ i, ν i = k → (Finset.univ.filter (fun s : Fin k → I => ∀ i, (List.ofFn s).count i = ν i)).card * ∏ i, (ν i).factorial = k.factorial := by sorry
