-- Prove2me | Theorems.Thm_GlobalTheory_ExpPow_int_eq_zero_of_exp_I_mul
-- name    : GlobalTheory.ExpPow.int_eq_zero_of_exp_I_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:07:15.587517+00:00
-- url     : https://prove2.me/theorems/6cbec363-1ad1-484d-85ee-dcdba296959e
-- title:
--   Exp Pow: int eq zero of exp I mul
-- statement:
--   The Exp Pow construction uses the int eq zero of exp I mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PowExpIOrInvInjective.lean#L5-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PowExpIOrInvInjective.lean#L5-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PowExpIOrInvInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ExpPow

theorem GlobalTheory.ExpPow.int_eq_zero_of_exp_I_mul (m : ℤ) (h : Complex.exp (Complex.I * m) = 1) : m = 0 := by sorry
