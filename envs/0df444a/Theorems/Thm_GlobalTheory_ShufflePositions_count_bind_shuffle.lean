-- Prove2me | Theorems.Thm_GlobalTheory_ShufflePositions_count_bind_shuffle
-- name    : GlobalTheory.ShufflePositions.count_bind_shuffle
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:11:27.42184+00:00
-- url     : https://prove2.me/theorems/8195c5b3-1d7a-490a-9171-7444ba5dcd9c
-- title:
--   Shuffle Positions: count bind shuffle
-- statement:
--   The Shuffle Positions construction uses the count bind shuffle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CountBindWordShuffleByPositions.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CountBindWordShuffleByPositions.lean#L107-L114

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

theorem GlobalTheory.ShufflePositions.count_bind_shuffle (A : Type) [DecidableEq A] (n : ℕ) (w : Fin n → A)
    (s₁ s₂ : Multiset (List A)) :
    (s₁.bind fun u => s₂.bind fun v => Shuffle.shuffle u v).count (List.ofFn w) =
      ∑ ε : Fin n → Bool, s₁.count (((List.finRange n).filter fun j => !ε j).map w) *
        s₂.count (((List.finRange n).filter ε).map w) := by sorry
