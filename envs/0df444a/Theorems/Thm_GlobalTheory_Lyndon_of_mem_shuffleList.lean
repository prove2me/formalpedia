-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_of_mem_shuffleList
-- name    : GlobalTheory.Lyndon.of_mem_shuffleList
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:20:12.381806+00:00
-- url     : https://prove2.me/theorems/8797360b-e854-470e-b116-7f414dc465cb
-- title:
--   Lyndon: of mem shuffle List
-- statement:
--   The Lyndon construction uses the of mem shuffle List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L519-L527
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L519-L527

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

theorem GlobalTheory.Lyndon.of_mem_shuffleList (L : List (List A)) :
    ∀ w ∈ shuffleList L, w.Perm L.flatten ∧ Interleaves w ↑L := by sorry
