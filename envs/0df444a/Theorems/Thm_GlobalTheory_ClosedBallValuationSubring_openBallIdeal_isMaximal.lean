-- Prove2me | Theorems.Thm_GlobalTheory_ClosedBallValuationSubring_openBallIdeal_isMaximal
-- name    : GlobalTheory.ClosedBallValuationSubring.openBallIdeal_isMaximal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:38.986868+00:00
-- url     : https://prove2.me/theorems/9c9e5d9a-c4a7-4027-97b6-f24c0a2801b9
-- title:
--   Closed Ball Valuation Subring: open Ball Ideal is Maximal
-- statement:
--   The Closed Ball Valuation Subring construction uses the open Ball Ideal is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ClosedBallValuationSubringToSubring.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ClosedBallValuationSubringToSubring.lean#L102-L104

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

theorem GlobalTheory.ClosedBallValuationSubring.openBallIdeal_isMaximal : (openBallIdeal K).IsMaximal := by sorry
