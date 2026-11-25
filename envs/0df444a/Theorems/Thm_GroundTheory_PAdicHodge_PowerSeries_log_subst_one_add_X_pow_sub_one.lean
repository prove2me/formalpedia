-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_PowerSeries_log_subst_one_add_X_pow_sub_one
-- name    : GroundTheory.PAdicHodge.PowerSeries.log_subst_one_add_X_pow_sub_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:45:24.266631+00:00
-- url     : https://prove2.me/theorems/b93a1d4c-94c1-448e-9754-c7db95e212f4
-- title:
--   Power Series: log subst one add X pow sub one
-- statement:
--   The Power Series construction uses the log subst one add X pow sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/LogPowSeries.lean#L32-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/LogPowSeries.lean#L32-L68

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

theorem GroundTheory.PAdicHodge.PowerSeries.log_subst_one_add_X_pow_sub_one (q : ℕ) :
    (log ℚ).subst ((1 + X : ℚ⟦X⟧) ^ q - 1) = (q : ℚ⟦X⟧) * log ℚ := by sorry
