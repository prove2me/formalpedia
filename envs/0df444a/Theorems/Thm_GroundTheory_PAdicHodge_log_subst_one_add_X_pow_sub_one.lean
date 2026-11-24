-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_log_subst_one_add_X_pow_sub_one
-- name    : GroundTheory.PAdicHodge.log_subst_one_add_X_pow_sub_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:38.84787+00:00
-- url     : https://prove2.me/theorems/7fa97406-852f-4df0-b9c2-d0851f312016
-- title:
--   PAdic Hodge: log subst one add X pow sub one
-- statement:
--   The PAdic Hodge construction uses the log subst one add X pow sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L206-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L206-L239

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_BdRSeries
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

theorem GroundTheory.PAdicHodge.log_subst_one_add_X_pow_sub_one (k : ℕ) :
    (log ℚ).subst ((1 + X) ^ k - 1 : ℚ⟦X⟧) = (k : ℚ⟦X⟧) * log ℚ := by sorry
