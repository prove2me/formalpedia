-- Prove2me | Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
-- name    : GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:02.94256+00:00
-- url     : https://prove2.me/theorems/2a942b27-85ee-490e-954d-fbd88b9bb4d0
-- title:
--   Bounded Power Series Disc: eval Bounded X
-- statement:
--   The Bounded Power Series Disc construction uses the eval Bounded X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SummableNormBoundedSeries.lean#L152-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SummableNormBoundedSeries.lean#L152-L154

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
variable {F : Type*} [NormedField F] [IsUltrametricDist F]
variable [CompleteSpace F]
variable (π : F) (hπ : ‖π‖ < 1)

theorem GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X : evalBounded π hπ ⟨X, X_mem_boundedSeries⟩ = π := by sorry
