-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_flatten_mem_shuffleList
-- name    : GlobalTheory.Lyndon.flatten_mem_shuffleList
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:19:46.430857+00:00
-- url     : https://prove2.me/theorems/53423794-47fe-42b1-a725-9d014fc597e7
-- title:
--   Lyndon: flatten mem shuffle List
-- statement:
--   The Lyndon construction uses the flatten mem shuffle List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L513-L516
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L513-L516

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
omit [LinearOrder A]

theorem GlobalTheory.Lyndon.flatten_mem_shuffleList (L : List (List A)) : L.flatten ∈ shuffleList L := by sorry
