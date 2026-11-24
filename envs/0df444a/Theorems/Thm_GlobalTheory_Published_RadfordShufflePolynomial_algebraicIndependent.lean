-- Prove2me | Theorems.Thm_GlobalTheory_Published_RadfordShufflePolynomial_algebraicIndependent
-- name    : GlobalTheory.Published.RadfordShufflePolynomial.algebraicIndependent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:28.378804+00:00
-- url     : https://prove2.me/theorems/940f12b1-63ac-47d2-8c46-4d0a808a105e
-- title:
--   Radford Shuffle Polynomial: algebraic Independent
-- statement:
--   The Radford Shuffle Polynomial construction uses the algebraic Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L681-L685
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L681-L685

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
open GlobalTheory.Published

theorem GlobalTheory.Published.RadfordShufflePolynomial.algebraicIndependent (h : RadfordShufflePolynomial)
    (K : Type) [Field K] [CharZero K] (A : Type) [LinearOrder A] :
    AlgebraicIndependent K
      (fun l : {w : List A // IsLyndon w} => ShuffleAlgebra.word K l.1) := by sorry
