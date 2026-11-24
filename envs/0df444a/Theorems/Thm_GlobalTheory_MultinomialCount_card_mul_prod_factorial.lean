-- Prove2me | Theorems.Thm_GlobalTheory_MultinomialCount_card_mul_prod_factorial
-- name    : GlobalTheory.MultinomialCount.card_mul_prod_factorial
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:29:37.626303+00:00
-- url     : https://prove2.me/theorems/c122f08e-ddc6-44d4-a360-fe81c89a8597
-- title:
--   Multinomial Count: card mul prod factorial
-- statement:
--   The Multinomial Count construction uses the card mul prod factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardMultisetWordsMulFactorial.lean#L32-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardMultisetWordsMulFactorial.lean#L32-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardMultisetWordsMulFactorial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical
open GlobalTheory GlobalTheory.MultinomialCount

theorem GlobalTheory.MultinomialCount.card_mul_prod_factorial : ∀ {I : Type} [Fintype I] (k : ℕ) (ν : I → ℕ), ∑ i, ν i = k →
    (Finset.univ.filter (fun s : Fin k → I => ∀ i, (List.ofFn s).count i = ν i)).card *
      ∏ i, (ν i).factorial = k.factorial := by sorry
