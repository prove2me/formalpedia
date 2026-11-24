-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DifferentConjugateDefects_span_natCast_ne_bot
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.span_natCast_ne_bot
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:15:05.664137+00:00
-- url     : https://prove2.me/theorems/ebf58130-aec9-418a-8b19-85b5a2feeaca
-- title:
--   Different Conjugate Defects: span nat Cast ne bot
-- statement:
--   The Different Conjugate Defects construction uses the span nat Cast ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SchurLatticeConjugates.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/SchurLatticeConjugates.lean#L26-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.span_natCast_ne_bot {K : Type} [Field K] [NumberField K] (n' : ℕ+) :
    Ideal.span {((n' : ℕ) : 𝓞 K)} ≠ ⊥ := by sorry
