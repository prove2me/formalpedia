-- Prove2me | Theorems.Thm_GlobalTheory_CoordScale_measurePreserving_inv_mul
-- name    : GlobalTheory.CoordScale.measurePreserving_inv_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:58:10.484967+00:00
-- url     : https://prove2.me/theorems/697d93bc-24ff-44ac-ac2b-efed66511141
-- title:
--   Coord Scale: measure Preserving inv mul
-- statement:
--   The Coord Scale construction uses the measure Preserving inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreimageReindexScaleComplexLe.lean#L20-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MeasurePreimageReindexScaleComplexLe.lean#L20-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreimageReindexScaleComplexLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoordScale
open MeasureTheory

theorem GlobalTheory.CoordScale.measurePreserving_inv_mul (r : ℝ) (hr : 0 < r) :
    MeasurePreserving (fun z : ℂ => ((r : ℂ))⁻¹ * z) volume
      (ENNReal.ofReal (r ^ 2) • (volume : Measure ℂ)) := by sorry
