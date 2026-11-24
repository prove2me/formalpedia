-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_sum_coeff_one_add_X_pow_sub_one_pow
-- name    : GroundTheory.PAdicHodge.sum_coeff_one_add_X_pow_sub_one_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:10.450256+00:00
-- url     : https://prove2.me/theorems/6d1aa7ce-e882-42ac-a539-7aa9be6c3241
-- title:
--   PAdic Hodge: sum coeff one add X pow sub one pow
-- statement:
--   The PAdic Hodge construction uses the sum coeff one add X pow sub one pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/LogPowSeries.lean#L75-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/LogPowSeries.lean#L75-L103

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

theorem GroundTheory.PAdicHodge.sum_coeff_one_add_X_pow_sub_one_pow (q : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ∑ n ∈ Finset.Icc 1 m, (-1 : ℚ) ^ (n - 1) / n *
      (((1 + Polynomial.X : Polynomial ℚ) ^ q - 1) ^ n).coeff m = (-1) ^ (m - 1) * q / m := by sorry
