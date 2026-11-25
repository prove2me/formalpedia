-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_log_near_one_unitaryGroup_of_form_linear_bound
-- name    : GlobalTheory.T.exists_log_near_one_unitaryGroup_of_form_linear_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:47.718419+00:00
-- url     : https://prove2.me/theorems/fe00feaf-bf61-5aba-b2bb-0854c5bd20df
-- title:
--   T: exists log near one unitary Group of form linear bound
-- statement:
--   The T construction uses the exists log near one unitary Group of form linear bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLogNearOneUnitaryGroupOfFormLinearBoundStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsLogNearOneUnitaryGroupOfFormLinearBoundStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLogNearOneUnitaryGroupOfFormLinearBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLogNearOneUnitaryGroupOfFormLinearBoundStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_log_near_one_unitaryGroup_of_form_linear_bound : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), IsUnit G.det → ∃ δ₁ C : ℝ, 0 < δ₁ ∧ ∀ (u : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ), uᴴ * G * u = G → δ ≤ δ₁ → (∀ i j, ‖(u - 1) i j‖ ≤ δ) → ∃ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 ∧ NormedSpace.exp X = u ∧ ∀ i j, ‖X i j‖ ≤ C * δ := by sorry
