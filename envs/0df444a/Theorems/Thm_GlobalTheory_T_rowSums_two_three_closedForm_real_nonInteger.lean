-- Prove2me | Theorems.Thm_GlobalTheory_T_rowSums_two_three_closedForm_real_nonInteger
-- name    : GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:13.056227+00:00
-- url     : https://prove2.me/theorems/eb984080-e315-4c3c-bd5d-9ec83885b241
-- title:
--   T: row Sums two three closed Form real non Integer
-- statement:
--   The T construction uses the row Sums two three closed Form real non Integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RowSumsTwoThreeClosedFormRealNonIntegerStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RowSumsTwoThreeClosedFormRealNonIntegerStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowSumsTwoThreeClosedFormRealNonInteger
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowSumsTwoThreeClosedFormRealNonIntegerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger : ∀ w : ℂ, w.im = 0 → (∀ n : ℤ, w ≠ n) → (∑' m : ℤ, 1 / (w + m) ^ 2 = (2 * (Real.pi : ℂ) * Complex.I) ^ 2 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 2)) ∧ ∑' m : ℤ, 1 / (w + m) ^ 3 = -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 3) := by sorry
