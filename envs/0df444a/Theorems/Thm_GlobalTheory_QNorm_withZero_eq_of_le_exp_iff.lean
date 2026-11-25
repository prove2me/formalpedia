-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_withZero_eq_of_le_exp_iff
-- name    : GlobalTheory.QNorm.withZero_eq_of_le_exp_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:07.39041+00:00
-- url     : https://prove2.me/theorems/8746f881-d162-48eb-be48-55b48d19b200
-- title:
--   QNorm: with Zero eq of le exp iff
-- statement:
--   The QNorm construction uses the with Zero eq of le exp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/WithZeroEqOfLeExpIff.lean#L8-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/WithZeroEqOfLeExpIff.lean#L8-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.withZero_eq_of_le_exp_iff {a b : ℤᵐ⁰} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by sorry
