-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_exists_sorted
-- name    : GlobalTheory.Lyndon.exists_sorted
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:48.508702+00:00
-- url     : https://prove2.me/theorems/8520dc0d-cc08-4d04-809b-23bf84926fd6
-- title:
--   Lyndon: exists sorted
-- statement:
--   The Lyndon construction uses the exists sorted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L427-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L427-L429

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

theorem GlobalTheory.Lyndon.exists_sorted (S : Multiset (List A)) :
    ∃ Q : List (List A), (Q : Multiset (List A)) = S ∧ Q.Pairwise (· ≥ ·) := by sorry
