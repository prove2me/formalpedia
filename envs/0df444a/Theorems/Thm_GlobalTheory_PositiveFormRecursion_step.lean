-- Prove2me | Theorems.Thm_GlobalTheory_PositiveFormRecursion_step
-- name    : GlobalTheory.PositiveFormRecursion.step
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:50:41.205581+00:00
-- url     : https://prove2.me/theorems/9de158bd-131e-432d-bafd-0e40ebfef4e1
-- title:
--   Positive Form Recursion: step
-- statement:
--   The Positive Form Recursion construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsBisSide.lean#L5-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsBisSide.lean#L5-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsBisSide
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PositiveFormRecursion

theorem GlobalTheory.PositiveFormRecursion.step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by sorry
