-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_log_pow_coeff_int
-- name    : GroundTheory.PAdicHodge.log_pow_coeff_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:45.635725+00:00
-- url     : https://prove2.me/theorems/ea91e9cc-c5f8-44c0-9618-0d764c2c3d67
-- title:
--   PAdic Hodge: log pow coeff int
-- statement:
--   The PAdic Hodge construction uses the log pow coeff int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/LogPowSeries.lean#L105-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/LogPowSeries.lean#L105-L131

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open PowerSeries

theorem GroundTheory.PAdicHodge.log_pow_coeff_int (q m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Finset.Icc 1 m, (-1 : ℤ) ^ (n - 1) *
      ((((1 : Polynomial ℤ) + Polynomial.X) ^ q - 1) ^ n).coeff m * ((m.factorial / n : ℕ) : ℤ) =
      (-1) ^ (m - 1) * q * (m - 1).factorial := by sorry
