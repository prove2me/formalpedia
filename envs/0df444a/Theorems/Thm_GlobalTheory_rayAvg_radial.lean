-- Prove2me | Theorems.Thm_GlobalTheory_rayAvg_radial
-- name    : GlobalTheory.rayAvg_radial
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:16:38.417894+00:00
-- url     : https://prove2.me/theorems/5719dec0-dbde-49c6-afdc-566f07afcc36
-- title:
--   Global Theory: ray Avg radial
-- statement:
--   The Global Theory construction uses the ray Avg radial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralUnitBallRayAverageLe.lean#L39-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LintegralUnitBallRayAverageLe.lean#L39-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralUnitBallRayAverageLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory

theorem GlobalTheory.rayAvg_radial (m : ℕ) {r : ℝ} (hr : 0 ≤ r) (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0:ℝ), (if r ≤ t then ENNReal.ofReal (r ^ (m + 1) / t ^ (m + 2)) * a else 0)
      ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) * a := by sorry
