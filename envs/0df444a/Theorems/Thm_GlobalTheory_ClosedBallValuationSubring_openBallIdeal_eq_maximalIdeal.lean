-- Prove2me | Theorems.Thm_GlobalTheory_ClosedBallValuationSubring_openBallIdeal_eq_maximalIdeal
-- name    : GlobalTheory.ClosedBallValuationSubring.openBallIdeal_eq_maximalIdeal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:48.542057+00:00
-- url     : https://prove2.me/theorems/6fe3120b-b7b4-46ee-94c8-c6c27eaa28cd
-- title:
--   Closed Ball Valuation Subring: open Ball Ideal eq maximal Ideal
-- statement:
--   The Closed Ball Valuation Subring construction uses the open Ball Ideal eq maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ClosedBallValuationSubringToSubring.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ClosedBallValuationSubringToSubring.lean#L97-L100

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
variable (K)

theorem GlobalTheory.ClosedBallValuationSubring.openBallIdeal_eq_maximalIdeal :
    openBallIdeal K = IsLocalRing.maximalIdeal (closedBallSubring K) := by sorry
