-- Prove2me | Theorems.Thm_GlobalTheory_ClosedBallValuationSubring_mem_closedBallSubring
-- name    : GlobalTheory.ClosedBallValuationSubring.mem_closedBallSubring
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:34.334057+00:00
-- url     : https://prove2.me/theorems/8db11009-b18a-4392-ab48-dc4502804c72
-- title:
--   Closed Ball Valuation Subring: mem closed Ball Subring
-- statement:
--   The Closed Ball Valuation Subring construction uses the mem closed Ball Subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ClosedBallValuationSubringToSubring.lean#L52-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ClosedBallValuationSubringToSubring.lean#L52-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ClosedBallValuationSubringToSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ClosedBallValuationSubring
variable (K : Type*) [NormedField K] [IsUltrametricDist K]
variable {K}

theorem GlobalTheory.ClosedBallValuationSubring.mem_closedBallSubring {x : K} : x ∈ closedBallSubring K ↔ ‖x‖ ≤ 1 := by sorry
