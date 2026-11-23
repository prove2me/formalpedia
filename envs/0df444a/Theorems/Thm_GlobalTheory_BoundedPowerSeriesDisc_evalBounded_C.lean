-- Prove2me | Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
-- name    : GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:58.37921+00:00
-- url     : https://prove2.me/theorems/ddd6fd12-1c97-424c-9786-bf6ca8d903eb
-- title:
--   Bounded Power Series Disc: eval Bounded C
-- statement:
--   The Bounded Power Series Disc construction uses the eval Bounded C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SummableNormBoundedSeries.lean#L147-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SummableNormBoundedSeries.lean#L147-L150

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

theorem GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C (c : F) :
    evalBounded π hπ ⟨C c, C_mem_boundedSeries c⟩ = c := by sorry
