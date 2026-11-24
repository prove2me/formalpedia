-- Prove2me | Theorems.Thm_GlobalTheory_MultinomialCount_ofFn_cons_count
-- name    : GlobalTheory.MultinomialCount.ofFn_cons_count
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:28:43.238433+00:00
-- url     : https://prove2.me/theorems/9cd19b5a-ad0c-4e7e-a8f4-b6fee62c0c6f
-- title:
--   Multinomial Count: of Fn cons count
-- statement:
--   The Multinomial Count construction uses the of Fn cons count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardMultisetWordsMulFactorial.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardMultisetWordsMulFactorial.lean#L6-L9

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

theorem GlobalTheory.MultinomialCount.ofFn_cons_count {I : Type} {k : ℕ} (a : I) (t : Fin k → I) (i : I) :
    (List.ofFn (Fin.cons a t : Fin (k+1) → I)).count i = (List.ofFn t).count i + if a = i then 1 else 0 := by sorry
