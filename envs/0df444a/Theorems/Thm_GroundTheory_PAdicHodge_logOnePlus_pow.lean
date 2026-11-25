-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_logOnePlus_pow
-- name    : GroundTheory.PAdicHodge.logOnePlus_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:42.209828+00:00
-- url     : https://prove2.me/theorems/ce1462a0-c59c-4520-abd9-9073c051f189
-- title:
--   PAdic Hodge: log One Plus pow
-- statement:
--   The PAdic Hodge construction uses the log One Plus pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L277-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L277-L281

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

theorem GroundTheory.PAdicHodge.logOnePlus_pow {z : B} (hz : z ∈ I) (k : ℕ) (hk : (1 + z) ^ k - 1 ∈ I) :
    logOnePlus I ((1 + z) ^ k - 1) hk = k * logOnePlus I z hz := by sorry
