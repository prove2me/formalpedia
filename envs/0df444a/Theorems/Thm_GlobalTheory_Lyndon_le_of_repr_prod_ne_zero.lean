-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_le_of_repr_prod_ne_zero
-- name    : GlobalTheory.Lyndon.le_of_repr_prod_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:05.329433+00:00
-- url     : https://prove2.me/theorems/c6d377f9-96e6-4cb3-90ac-e7580da2589a
-- title:
--   Lyndon: le of repr prod ne zero
-- statement:
--   The Lyndon construction uses the le of repr prod ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L559-L567
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L559-L567

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
open ShuffleAlgebra
variable (K : Type) [Field K]

theorem GlobalTheory.Lyndon.le_of_repr_prod_ne_zero {L : List (List A)} (hL : IsFactors L) {w : List A}
    (h : (wordBasis K A).repr (L.map (word K)).prod w ≠ 0) :
    w.Perm L.flatten ∧ w ≤ L.flatten := by sorry
