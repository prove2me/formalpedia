-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_unit_minor_of_integral_matrix
-- name    : GlobalTheory.T.exists_unit_minor_of_integral_matrix
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:31:23.578994+00:00
-- url     : https://prove2.me/theorems/16b07127-ba06-4e5d-947d-0bc780c2d5b0
-- title:
--   T: exists unit minor of integral matrix
-- statement:
--   The T construction uses the exists unit minor of integral matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitMinorOfIntegralMatrixStatement.lean#L5-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitMinorOfIntegralMatrixStatement.lean#L5-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitMinorOfIntegralMatrix
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitMinorOfIntegralMatrixStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_unit_minor_of_integral_matrix : ∀ (p : ℕ) [Fact p.Prime] {κ J : Type} [Fintype κ] [DecidableEq κ] [Fintype J] (c : Matrix κ J ℂ_[p]),
  (∀ k i, ‖c k i‖ ≤ 1) →
  (∀ a : κ → ℂ_[p], (∀ i, ‖∑ k, a k * c k i‖ ≤ 1) → ∀ k, ‖a k‖ ≤ 1) →
  ∃ f : κ → J, Function.Injective f ∧ ‖(c.submatrix id f).det‖ = 1 := by sorry
