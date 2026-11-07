-- Prove2me | Theorems.Thm_LevyFoundations_leanlevy_chat16_compensated_integral_continuous
-- name    : LevyFoundations.leanlevy_chat16_compensated_integral_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:46:49.405201+00:00
-- url     : https://prove2.me/theorems/fa712307-d7c9-4e4a-91f0-4425f7ad0857
-- title:
--   Continuity of the compensated Levy jump integral
-- statement:
--   The compensated jump integral defining the Levy characteristic exponent varies continuously with real frequency. A local quadratic bound against the Levy measure integrability envelope supports dominated convergence.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineProof.lean lines 533-556, continuous_integral_levyCompensatedIntegrand.

import Mathlib
import Definitions.Def_levy_foundations_isLevyMeasure
import Definitions.Def_levy_foundations_compensatedIntegrand
open MeasureTheory

theorem LevyFoundations.leanlevy_chat16_compensated_integral_continuous
    {ν : Measure ℝ} (hν : LevyFoundations.isLevyMeasure ν) :
    Continuous (fun ξ : ℝ => ∫ x, LevyFoundations.compensatedIntegrand ξ x ∂ν) := by sorry
