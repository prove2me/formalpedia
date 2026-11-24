-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_word_mem_of_lyndon_mem
-- name    : GlobalTheory.Lyndon.word_mem_of_lyndon_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:19:59.085793+00:00
-- url     : https://prove2.me/theorems/f44deb0a-06f0-436f-a109-668bc34ebd46
-- title:
--   Lyndon: word mem of lyndon mem
-- statement:
--   The Lyndon construction uses the word mem of lyndon mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L569-L606
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L569-L606

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Shuffle
open GlobalTheory.Lyndon
variable {A : Type} [LinearOrder A]
open ShuffleAlgebra
variable (K : Type) [Field K]

theorem GlobalTheory.Lyndon.word_mem_of_lyndon_mem [CharZero K] (B : Subalgebra K (ShuffleAlgebra K A))
    (hB : ∀ l, IsLyndon l → word K l ∈ B) (w : List A) : word K w ∈ B := by sorry
