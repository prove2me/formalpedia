-- Prove2me | Theorems.Thm_GlobalTheory_hsGrowth_log_floor_le
-- name    : GlobalTheory.hsGrowth_log_floor_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:55:14.267649+00:00
-- url     : https://prove2.me/theorems/0677ae49-079b-46f7-9027-bd956ed76416
-- title:
--   Global Theory: hs Growth log floor le
-- statement:
--   The Global Theory construction uses the hs Growth log floor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CountGrowthExponentialRadii.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CountGrowthExponentialRadii.lean#L15-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TendstoRankDivPowOfChooseBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CountGrowthExponentialRadii
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory

theorem GlobalTheory.hsGrowth_log_floor_le {Y : ℝ} (hY : 0 < Y) :
    Real.log ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log 3 + |Real.log Y| := by sorry
