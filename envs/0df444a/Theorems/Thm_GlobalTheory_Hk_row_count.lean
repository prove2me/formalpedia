-- Prove2me | Theorems.Thm_GlobalTheory_Hk_row_count
-- name    : GlobalTheory.Hk.row_count
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:36:34.593152+00:00
-- url     : https://prove2.me/theorems/9e0df148-9302-4ebc-bab6-261589cfd7ef
-- title:
--   Hk: row count
-- statement:
--   The Hk construction uses the row count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QFormCount.lean#L176-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QFormCount.lean#L176-L213

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk

theorem GlobalTheory.Hk.row_count (α c y : ℝ) (hα : 0 < α) :
    ∃ F : Finset ℤ, (∀ m : ℤ, m ∈ F ↔ α * (m + c) ^ 2 ≤ y) ∧
      |(F.card : ℝ) - 2 * Real.sqrt (y / α)| ≤ 1 := by sorry
