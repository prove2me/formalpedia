-- Prove2me | Theorems.Thm_GlobalTheory_log_add_rpow_mul_log_pow_le_rpow
-- name    : GlobalTheory.log_add_rpow_mul_log_pow_le_rpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:01.384817+00:00
-- url     : https://prove2.me/theorems/ebfe5757-7278-4285-8d63-ad67012adabf
-- title:
--   Global Theory: log add rpow mul log pow le rpow
-- statement:
--   The Global Theory construction uses the log add rpow mul log pow le rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogAddRpowMulLogPowLeRpow.lean#L9-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogAddRpowMulLogPowLeRpow.lean#L9-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogAddRpowMulLogPowLeRpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open GlobalTheory
open Filter Asymptotics

theorem GlobalTheory.log_add_rpow_mul_log_pow_le_rpow :
    ∀ a b c C κ : ℝ, ∀ p : ℕ, 0 ≤ a → a < b → 0 < κ → ∃ x0 : ℝ, ∀ x ≥ x0,
      c * Real.log x + C * x ^ a * Real.log x ^ p + C ≤ κ * x ^ b := by sorry
