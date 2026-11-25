-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_logOnePlus_mem
-- name    : GroundTheory.PAdicHodge.logOnePlus_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:43.274737+00:00
-- url     : https://prove2.me/theorems/1df8dd74-9fbc-4aeb-bf97-90100ccb9d01
-- title:
--   PAdic Hodge: log One Plus mem
-- statement:
--   The PAdic Hodge construction uses the log One Plus mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L263-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BdRSeries.lean#L263-L264

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

theorem GroundTheory.PAdicHodge.logOnePlus_mem {z : B} (hz : z ∈ I) : logOnePlus I z hz ∈ I := by sorry
