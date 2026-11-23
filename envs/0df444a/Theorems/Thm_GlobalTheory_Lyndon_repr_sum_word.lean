-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_repr_sum_word
-- name    : GlobalTheory.Lyndon.repr_sum_word
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:07.198788+00:00
-- url     : https://prove2.me/theorems/e123baf8-43a3-4f5a-92ca-b71f48fd41a8
-- title:
--   Lyndon: repr sum word
-- statement:
--   The Lyndon construction uses the repr sum word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L543-L552
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L543-L552

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

theorem GlobalTheory.Lyndon.repr_sum_word (s : Multiset (List A)) (w : List A) :
    (wordBasis K A).repr (s.map (word K)).sum w = (s.count w : K) := by sorry
