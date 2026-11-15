-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaLevyMeasure_isLevyMeasure
-- name    : Kyprianou.Ch01.gammaLevyMeasure_isLevyMeasure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:14:38.879849+00:00
-- url     : https://prove2.me/theorems/a355d619-5a22-43ad-9424-3b21cbff874d
-- title:
--   The gamma jump intensity satisfies the Lévy measure integrability condition
-- statement:
--   For positive alpha and beta the gamma intensity beta exp(-alpha*x)/x on positive x vanishes at zero and has finite integral of min(1,x^2).
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.4, original gamma Lévy exponent theorem 32009c4f-2a5e-4668-b3b2-28639144a632.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaLevyMeasure_isLevyMeasure
    (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta) :
    IsLevyMeasure (gammaLevyMeasure alpha beta) := by sorry
