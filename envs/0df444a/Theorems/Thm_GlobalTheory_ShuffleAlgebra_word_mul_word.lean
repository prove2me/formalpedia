-- Prove2me | Theorems.Thm_GlobalTheory_ShuffleAlgebra_word_mul_word
-- name    : GlobalTheory.ShuffleAlgebra.word_mul_word
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:42.324447+00:00
-- url     : https://prove2.me/theorems/497b2782-5807-44bf-b843-abf0fe118ea1
-- title:
--   Shuffle Algebra: word mul word
-- statement:
--   The Shuffle Algebra construction uses the word mul word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L164-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L164-L165

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
open GlobalTheory.ShuffleAlgebra
variable (K : Type) [CommRing K] {A : Type}

theorem GlobalTheory.ShuffleAlgebra.word_mul_word (u v : List A) :
    word K u * word K v = ((shuffle u v).map (word K)).sum := by sorry
