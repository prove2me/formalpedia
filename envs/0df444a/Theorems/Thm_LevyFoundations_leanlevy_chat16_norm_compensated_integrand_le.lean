-- Prove2me | Theorems.Thm_LevyFoundations_leanlevy_chat16_norm_compensated_integrand_le
-- name    : LevyFoundations.leanlevy_chat16_norm_compensated_integrand_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:50:15.11646+00:00
-- url     : https://prove2.me/theorems/88fed74e-a4f8-49c5-8cba-967aac356c75
-- title:
--   Quadratic Levy compensation envelope
-- statement:
--   The compensated complex jump integrand is bounded by a universal quadratic-frequency multiple of the Lévy measure's integrable min(1,x²) envelope.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/CompensatedIntegral.lean lines 86-137, norm_levyCompensatedIntegrand_le and le_two.

import Mathlib
import Definitions.Def_levy_foundations_compensatedIntegrand
open MeasureTheory Complex

theorem LevyFoundations.leanlevy_chat16_norm_compensated_integrand_le
    (ξ x : ℝ) :
    ‖LevyFoundations.compensatedIntegrand ξ x‖ ≤
      (2 + 3 * ξ ^ 2) * min 1 (x ^ 2) := by sorry
