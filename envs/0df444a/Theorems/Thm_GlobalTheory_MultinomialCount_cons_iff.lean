-- Prove2me | Theorems.Thm_GlobalTheory_MultinomialCount_cons_iff
-- name    : GlobalTheory.MultinomialCount.cons_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:29:37.073006+00:00
-- url     : https://prove2.me/theorems/2b851b02-4c8c-4eeb-a481-b2d237cda341
-- title:
--   Multinomial Count: cons iff
-- statement:
--   The Multinomial Count construction uses the cons iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardMultisetWordsMulFactorial.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardMultisetWordsMulFactorial.lean#L11-L30

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

theorem GlobalTheory.MultinomialCount.cons_iff {I : Type} {k : ℕ} (ν : I → ℕ) (a : I) (t : Fin k → I) :
    (∀ i, (List.ofFn (Fin.cons a t : Fin (k+1) → I)).count i = ν i) ↔
      (1 ≤ ν a ∧ ∀ i, (List.ofFn t).count i = Function.update ν a (ν a - 1) i) := by sorry
