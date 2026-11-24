-- Prove2me | Theorems.Thm_GlobalTheory_GLFirstColumn_exists_section
-- name    : GlobalTheory.GLFirstColumn.exists_section
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:15.806593+00:00
-- url     : https://prove2.me/theorems/bfeab9c9-83b4-4eed-8396-753865249428
-- title:
--   GLFirst Column: exists section
-- statement:
--   The GLFirst Column construction uses the exists section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L214-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreservingCons.lean#L214-L265

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.GLFirstColumn

theorem GlobalTheory.GLFirstColumn.exists_section (k : ℕ) (hk : 1 ≤ k) :
    ∃ s : (Fin (k + 1) → ℂ) → Fin (k + 1) → Fin (k + 1) → ℂ, Measurable s ∧
      ∀ x, x ≠ 0 → (Matrix.of (s x)).det = 1 ∧ ∀ a, s x a 0 = x a := by sorry
