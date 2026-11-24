-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_exists_cut
-- name    : GlobalTheory.Lyndon.exists_cut
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:21:50.712036+00:00
-- url     : https://prove2.me/theorems/e5b384cf-eb3a-46c5-b9a0-0ffe8c60c120
-- title:
--   Lyndon: exists cut
-- statement:
--   The Lyndon construction uses the exists cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L409-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L409-L425

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

theorem GlobalTheory.Lyndon.exists_cut (m : List A) (F : List (List A)) (hF : F.Pairwise (· ≥ ·)) :
    ∃ P R, F = P ++ R ∧ (∀ f ∈ P, m ≤ f) ∧ ∀ f ∈ R, f ≤ m := by sorry
