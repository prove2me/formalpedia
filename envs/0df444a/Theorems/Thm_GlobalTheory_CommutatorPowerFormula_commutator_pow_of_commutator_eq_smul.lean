-- Prove2me | Theorems.Thm_GlobalTheory_CommutatorPowerFormula_commutator_pow_of_commutator_eq_smul
-- name    : GlobalTheory.CommutatorPowerFormula.commutator_pow_of_commutator_eq_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:48.231056+00:00
-- url     : https://prove2.me/theorems/3350434a-7666-51c0-b229-2ffce9f25627
-- title:
--   Commutator Power Formula: commutator pow of commutator eq smul
-- statement:
--   The Commutator Power Formula construction uses the commutator pow of commutator eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommutatorPowOfCommutatorEqSmul.lean#L5-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CommutatorPowOfCommutatorEqSmul.lean#L5-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommutatorPowOfCommutatorEqSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CommutatorPowerFormula

theorem GlobalTheory.CommutatorPowerFormula.commutator_pow_of_commutator_eq_smul {A : Type} [Ring A] [Algebra ℚ A] {H X : A} {s : ℚ}
    (h : H * X - X * H = s • X) (k : ℕ) :
    H * X ^ k - X ^ k * H = ((k : ℚ) * s) • X ^ k := by sorry
