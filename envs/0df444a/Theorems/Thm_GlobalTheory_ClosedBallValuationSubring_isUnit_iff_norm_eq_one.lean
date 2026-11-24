-- Prove2me | Theorems.Thm_GlobalTheory_ClosedBallValuationSubring_isUnit_iff_norm_eq_one
-- name    : GlobalTheory.ClosedBallValuationSubring.isUnit_iff_norm_eq_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:13:42.386313+00:00
-- url     : https://prove2.me/theorems/47ca7ad7-d192-4ed8-b4ce-37bbdb1b301d
-- title:
--   Closed Ball Valuation Subring: is Unit iff norm eq one
-- statement:
--   The Closed Ball Valuation Subring construction uses the is Unit iff norm eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ClosedBallValuationSubringToSubring.lean#L57-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ClosedBallValuationSubringToSubring.lean#L57-L84

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

theorem GlobalTheory.ClosedBallValuationSubring.isUnit_iff_norm_eq_one {x : closedBallSubring K} : IsUnit x ↔ ‖(x : K)‖ = 1 := by sorry
