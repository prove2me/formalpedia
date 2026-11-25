-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_one_add_X_mul_mk_neg_one_pow
-- name    : GroundTheory.PAdicHodge.one_add_X_mul_mk_neg_one_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:16.233103+00:00
-- url     : https://prove2.me/theorems/c4b95dd6-b957-4880-a164-4635f5b9936f
-- title:
--   PAdic Hodge: one add X mul mk neg one pow
-- statement:
--   The PAdic Hodge construction uses the one add X mul mk neg one pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/LogPowSeries.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/LogPowSeries.lean#L20-L27

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

theorem GroundTheory.PAdicHodge.one_add_X_mul_mk_neg_one_pow :
    (1 + X : ℚ⟦X⟧) * mk (fun n => algebraMap ℚ ℚ ((-1 : ℚ) ^ n)) = 1 := by sorry
