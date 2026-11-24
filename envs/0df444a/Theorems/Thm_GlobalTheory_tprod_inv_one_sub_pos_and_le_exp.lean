-- Prove2me | Theorems.Thm_GlobalTheory_tprod_inv_one_sub_pos_and_le_exp
-- name    : GlobalTheory.tprod_inv_one_sub_pos_and_le_exp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:24.285426+00:00
-- url     : https://prove2.me/theorems/7dd1a62e-5122-497e-8eaf-6d52daf28430
-- title:
--   Global Theory: tprod inv one sub pos and le exp
-- statement:
--   The Global Theory construction uses the tprod inv one sub pos and le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsLogInvOneSubLeTwoMulAbs.lean#L24-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AbsLogInvOneSubLeTwoMulAbs.lean#L24-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsLogInvOneSubLeTwoMulAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory IsDedekindDomain NumberField
open GlobalTheory

theorem GlobalTheory.tprod_inv_one_sub_pos_and_le_exp :
    ∀ {ι : Type} (y : ι → ℝ) (B : ℝ), (∀ a, |y a| ≤ 1 / 2) → Summable (fun a => |y a|) →
      ∑' a, |y a| ≤ B →
      0 < ∏' a, (1 - y a)⁻¹ ∧ ∏' a, (1 - y a)⁻¹ ≤ Real.exp (2 * B) := by sorry
