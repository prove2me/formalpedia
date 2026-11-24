-- Prove2me | Theorems.Thm_GlobalTheory_ShufflePositions_pos_cons
-- name    : GlobalTheory.ShufflePositions.pos_cons
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:11:30.737899+00:00
-- url     : https://prove2.me/theorems/e17ec131-9e16-4c20-9cbc-f9e260f716eb
-- title:
--   Shuffle Positions: pos cons
-- statement:
--   The Shuffle Positions construction uses the pos cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CountBindWordShuffleByPositions.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CountBindWordShuffleByPositions.lean#L23-L30

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
omit [DecidableEq A]

theorem GlobalTheory.ShufflePositions.pos_cons {n : ℕ} (w : Fin (n + 1) → A) (p : Fin (n + 1) → Bool) :
    ((List.finRange (n + 1)).filter p).map w =
      (if p 0 then [w 0] else []) ++
        ((List.finRange n).filter fun j => p j.succ).map (fun j => w j.succ) := by sorry
