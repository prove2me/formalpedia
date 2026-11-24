-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_exists_suffix_le
-- name    : GlobalTheory.Lyndon.exists_suffix_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:19:34.743052+00:00
-- url     : https://prove2.me/theorems/176b93e4-6626-41d7-9ce8-af8aabc0cac7
-- title:
--   Lyndon: exists suffix le
-- statement:
--   The Lyndon construction uses the exists suffix le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L276-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L276-L290

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

theorem GlobalTheory.Lyndon.exists_suffix_le (l : List A) (L : List (List A)) (hL : ∀ m ∈ L, m ≤ l) :
    ∀ t r : List A, t ≠ [] → t ++ r = L.flatten → ∃ s q, q ≠ [] ∧ t = s ++ q ∧ q ≤ l := by sorry
