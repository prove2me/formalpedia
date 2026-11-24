-- Prove2me | Theorems.Thm_GlobalTheory_differentiableOn_doublingIterate
-- name    : GlobalTheory.differentiableOn_doublingIterate
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:18.738319+00:00
-- url     : https://prove2.me/theorems/ac2caaef-7c70-4da3-a9f9-4a39d0880c16
-- title:
--   Global Theory: differentiable On doubling Iterate
-- statement:
--   The Global Theory construction uses the differentiable On doubling Iterate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnDoublingIterate.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnDoublingIterate.lean#L33-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnDoublingIterate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.differentiableOn_doublingIterate {h : E → ℂ} {r : ℝ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 r)) (n : ℕ) :
    DifferentiableOn ℂ (doublingIterate h n) (Metric.ball 0 r) := by sorry
