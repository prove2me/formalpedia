-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_logOnePlus_sub_sum_mem
-- name    : GroundTheory.PAdicHodge.logOnePlus_sub_sum_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:47:12.043347+00:00
-- url     : https://prove2.me/theorems/1711ead4-e38e-4d16-abcd-670fcf2b6b2c
-- title:
--   PAdic Hodge: log One Plus sub sum mem
-- statement:
--   The PAdic Hodge construction uses the log One Plus sub sum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L248-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L248-L261

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
variable {B : Type*} [CommRing B] [Algebra ℚ B] {I : Ideal B} [IsAdicComplete I B]

theorem GroundTheory.PAdicHodge.logOnePlus_sub_sum_mem {z : B} (hz : z ∈ I) (n : ℕ) :
    logOnePlus I z hz - ∑ i ∈ Finset.Ico 1 n, algebraMap ℚ B ((-1) ^ (i + 1) / i) * z ^ i ∈
      I ^ n := by sorry
