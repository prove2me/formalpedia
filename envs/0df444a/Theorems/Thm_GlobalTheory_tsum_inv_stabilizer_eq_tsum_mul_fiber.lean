-- Prove2me | Theorems.Thm_GlobalTheory_tsum_inv_stabilizer_eq_tsum_mul_fiber
-- name    : GlobalTheory.tsum_inv_stabilizer_eq_tsum_mul_fiber
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:52:51.408218+00:00
-- url     : https://prove2.me/theorems/da0cb292-744d-5679-a727-f92ac9a4b548
-- title:
--   Global Theory: tsum inv stabilizer eq tsum mul fiber
-- statement:
--   The Global Theory construction uses the tsum inv stabilizer eq tsum mul fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TsumInvStabilizerEqTsumMulFiber.lean#L98-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TsumInvStabilizerEqTsumMulFiber.lean#L98-L159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TsumInvStabilizerEqTsumMulFiber
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal
open GlobalTheory
open MulAction

theorem GlobalTheory.tsum_inv_stabilizer_eq_tsum_mul_fiber {Γ L Y : Type} [Group Γ] [MulAction Γ L]
    [MulAction Γ Y] (π : L → Y) (hπ : ∀ (g : Γ) (x : L), π (g • x) = g • π x)
    (hfin : ∀ y : Y, (∃ x, π x = y) → Finite (MulAction.stabilizer Γ y)) :
    (∑' o : MulAction.orbitRel.Quotient Γ L,
        (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹)
      = ∑' o : MulAction.orbitRel.Quotient Γ Y,
        (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹
          * (((π ⁻¹' {o.out}).encard : ℝ≥0∞)) := by sorry
