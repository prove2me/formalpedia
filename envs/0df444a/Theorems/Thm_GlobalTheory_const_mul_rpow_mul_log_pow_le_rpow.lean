-- Prove2me | Theorems.Thm_GlobalTheory_const_mul_rpow_mul_log_pow_le_rpow
-- name    : GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:57.216827+00:00
-- url     : https://prove2.me/theorems/ead4d636-27a3-4e0f-ba24-6425df47794e
-- title:
--   Global Theory: const mul rpow mul log pow le rpow
-- statement:
--   The Global Theory construction uses the const mul rpow mul log pow le rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConstMulRpowMulLogPowLeRpow.lean#L9-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ConstMulRpowMulLogPowLeRpow.lean#L9-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConstMulRpowMulLogPowLeRpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real Filter Asymptotics
open GlobalTheory
open Real Filter Asymptotics

theorem GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow :
    ∀ a b C : ℝ, ∀ p : ℕ, a < b →
      ∃ x0 : ℝ, ∀ x ≥ x0, C * x ^ a * Real.log x ^ p ≤ x ^ b := by sorry
