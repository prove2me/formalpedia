-- Prove2me | Theorems.Thm_GlobalTheory_ShufflePositions_count_single
-- name    : GlobalTheory.ShufflePositions.count_single
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:11:20.745829+00:00
-- url     : https://prove2.me/theorems/9fe619d1-97f5-4c19-ac72-241a64b16692
-- title:
--   Shuffle Positions: count single
-- statement:
--   The Shuffle Positions construction uses the count single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CountBindWordShuffleByPositions.lean#L48-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CountBindWordShuffleByPositions.lean#L48-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CountBindWordShuffleByPositions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory
open GlobalTheory.ShufflePositions
variable {A : Type} [DecidableEq A]

theorem GlobalTheory.ShufflePositions.count_single (n : ℕ) : ∀ (w : Fin n → A) (u v : List A),
    (Shuffle.shuffle u v).count (List.ofFn w) =
      ∑ ε : Fin n → Bool,
        ({u} : Multiset (List A)).count (((List.finRange n).filter fun j => !ε j).map w) *
        ({v} : Multiset (List A)).count (((List.finRange n).filter ε).map w) := by sorry
