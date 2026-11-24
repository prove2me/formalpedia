-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_exists_suffix_le_of_mem
-- name    : GlobalTheory.Lyndon.exists_suffix_le_of_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:19:34.128739+00:00
-- url     : https://prove2.me/theorems/46a79f67-32c1-4ad4-b9bd-94c6eff7d701
-- title:
--   Lyndon: exists suffix le of mem
-- statement:
--   The Lyndon construction uses the exists suffix le of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L399-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L399-L407

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

theorem GlobalTheory.Lyndon.exists_suffix_le_of_mem {F : List (List A)} (hF : IsFactors F) {f : List A} (hf : f ∈ F) :
    ∃ s g, g ≠ [] ∧ F.flatten = s ++ g ∧ g ≤ f := by sorry
