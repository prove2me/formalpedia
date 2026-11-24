-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Segments_shufcomb
-- name    : GlobalTheory.CompanionTheory.Segments.shufcomb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:12:24.82944+00:00
-- url     : https://prove2.me/theorems/4cc567d4-3f86-4cd6-a0af-8e8533f8a13f
-- title:
--   Segments: shufcomb
-- statement:
--   The Segments construction uses the shufcomb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StrictAntiOfTwoExceptions.lean#L5-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/StrictAntiOfTwoExceptions.lean#L5-L46

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_StrictAntiOfTwoExceptions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Segments

theorem GlobalTheory.CompanionTheory.Segments.shufcomb (l : ℕ) (hl : 3 ≤ l) (w : Fin l → ℕ) (hw : ∀ a, w a < l) (i j : Fin l)
    (hi : w i = 0) (hj : w j = l - 1)
    (h1 : ∀ a b, a < b → a ≠ i → b ≠ i → w b < w a)
    (h2 : ∀ a b, a < b → a ≠ j → b ≠ j → w b < w a) : StrictAnti w := by sorry
