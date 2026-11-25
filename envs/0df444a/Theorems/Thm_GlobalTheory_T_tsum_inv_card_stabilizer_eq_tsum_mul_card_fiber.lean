-- Prove2me | Theorems.Thm_GlobalTheory_T_tsum_inv_card_stabilizer_eq_tsum_mul_card_fiber
-- name    : GlobalTheory.T.tsum_inv_card_stabilizer_eq_tsum_mul_card_fiber
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:23.051185+00:00
-- url     : https://prove2.me/theorems/353c52af-ed3d-45f7-971c-218b6f850d6d
-- title:
--   T: tsum inv card stabilizer eq tsum mul card fiber
-- statement:
--   The T construction uses the tsum inv card stabilizer eq tsum mul card fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TsumInvStabilizerEqTsumMulFiberStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TsumInvStabilizerEqTsumMulFiberStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TsumInvStabilizerEqTsumMulFiber
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TsumInvStabilizerEqTsumMulFiberStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.tsum_inv_card_stabilizer_eq_tsum_mul_card_fiber : ∀ {Γ L Y : Type} [Group Γ] [MulAction Γ L] [MulAction Γ Y] (π : L → Y), (∀ (g : Γ) (x : L), π (g • x) = g • π x) → (∀ y : Y, (∃ x, π x = y) → Finite (MulAction.stabilizer Γ y)) → (∑' o : MulAction.orbitRel.Quotient Γ L, (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹) = ∑' o : MulAction.orbitRel.Quotient Γ Y, (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹ * (((π ⁻¹' {o.out}).encard : ℝ≥0∞)) := by sorry
