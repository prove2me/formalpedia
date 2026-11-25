-- Prove2me | Theorems.Thm_GlobalTheory_HodgeCurvPoint_sum_norm_sq
-- name    : GlobalTheory.HodgeCurvPoint.sum_norm_sq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:49:00.2676+00:00
-- url     : https://prove2.me/theorems/4017d54d-587a-444d-976a-033abef4d63a
-- title:
--   Hodge Curv Point: sum norm sq
-- statement:
--   The Hodge Curv Point construction uses the sum norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeCurvatureDualMetricPointwiseBound.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeCurvatureDualMetricPointwiseBound.lean#L41-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeCurvPoint
variable {g : ℕ}

theorem GlobalTheory.HodgeCurvPoint.sum_norm_sq (v : Fin g → ℂ) : ∑ j, ‖v j‖ ^ 2 =
    (fun j => (v j).re) ⬝ᵥ (fun j => (v j).re) + (fun j => (v j).im) ⬝ᵥ (fun j => (v j).im) := by sorry
