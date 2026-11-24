-- Prove2me | Theorems.Thm_GlobalTheory_isLyndon_of_pairwise_lt
-- name    : GlobalTheory.isLyndon_of_pairwise_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:51.879658+00:00
-- url     : https://prove2.me/theorems/ec8d190e-2ac0-4406-950b-5235b78b5582
-- title:
--   Global Theory: is Lyndon of pairwise lt
-- statement:
--   The Global Theory construction uses the is Lyndon of pairwise lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L175-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L175-L181

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

theorem GlobalTheory.isLyndon_of_pairwise_lt {A : Type} [LinearOrder A] {w : List A} (hw : w ≠ [])
    (h : w.Pairwise (· < ·)) : IsLyndon w := by sorry
