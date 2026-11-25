-- Prove2me | Theorems.Thm_GlobalTheory_T_inv_sq_le_wignerCoeffSqLowering
-- name    : GlobalTheory.T.inv_sq_le_wignerCoeffSqLowering
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:35:14.449801+00:00
-- url     : https://prove2.me/theorems/42cbf705-0824-476a-9314-c12eef982782
-- title:
--   T: inv sq le wigner Coeff Sq Lowering
-- statement:
--   The T construction uses the inv sq le wigner Coeff Sq Lowering property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/InvSqLeWignerCoeffSqLoweringStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/InvSqLeWignerCoeffSqLoweringStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvSqLeWignerCoeffSqLowering
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvSqLeWignerCoeffSqLoweringStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.inv_sq_le_wignerCoeffSqLowering : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ), StrictAnti L → (∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) → (∀ j, M j ≠ L l) → 1 ≤ D → ((L 0 : ℝ) - L l ≤ D) → ((L l : ℝ) - L (Fin.last n) ≤ D) → (D ^ 2)⁻¹ ≤ GlobalTheory.WigSh.wM L M l := by sorry
