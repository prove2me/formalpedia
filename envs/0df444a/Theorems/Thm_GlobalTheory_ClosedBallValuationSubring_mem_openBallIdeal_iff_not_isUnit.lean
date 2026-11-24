-- Prove2me | Theorems.Thm_GlobalTheory_ClosedBallValuationSubring_mem_openBallIdeal_iff_not_isUnit
-- name    : GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal_iff_not_isUnit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:49.329804+00:00
-- url     : https://prove2.me/theorems/258b6665-9530-47e2-880f-ccdcbb137e82
-- title:
--   Closed Ball Valuation Subring: mem open Ball Ideal iff not is Unit
-- statement:
--   The Closed Ball Valuation Subring construction uses the mem open Ball Ideal iff not is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ClosedBallValuationSubringToSubring.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ClosedBallValuationSubringToSubring.lean#L86-L90

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

theorem GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal_iff_not_isUnit {x : closedBallSubring K} :
    x ∈ openBallIdeal K ↔ ¬ IsUnit x := by sorry
