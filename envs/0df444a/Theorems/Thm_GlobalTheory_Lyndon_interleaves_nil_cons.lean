-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_interleaves_nil_cons
-- name    : GlobalTheory.Lyndon.interleaves_nil_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:31.162462+00:00
-- url     : https://prove2.me/theorems/00a1e7e0-2a48-4481-b00c-875559ec3cc6
-- title:
--   Lyndon: interleaves nil cons
-- statement:
--   The Lyndon construction uses the interleaves nil cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L329-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L329-L344

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

theorem GlobalTheory.Lyndon.interleaves_nil_cons (w : List A) :
    ∀ S : Multiset (List A), Interleaves w ([] ::ₘ S) ↔ Interleaves w S := by sorry
