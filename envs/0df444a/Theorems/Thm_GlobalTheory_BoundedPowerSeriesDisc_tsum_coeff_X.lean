-- Prove2me | Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_tsum_coeff_X
-- name    : GlobalTheory.BoundedPowerSeriesDisc.tsum_coeff_X
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:01:29.895993+00:00
-- url     : https://prove2.me/theorems/5f39d44f-ea35-4ffc-93b7-b8e98e0cfef9
-- title:
--   Bounded Power Series Disc: tsum coeff X
-- statement:
--   The Bounded Power Series Disc construction uses the tsum coeff X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SummableNormBoundedSeries.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SummableNormBoundedSeries.lean#L35-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BoundedPowerSeriesDisc
open PowerSeries
variable {K : Type*} [NormedField K]

theorem GlobalTheory.BoundedPowerSeriesDisc.tsum_coeff_X (t : K) : ∑' n, coeff n (X : K⟦X⟧) * t ^ n = t := by sorry
