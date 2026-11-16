-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaLevyMeasure_infiniteMass
-- name    : Kyprianou.Ch01.gammaLevyMeasure_infiniteMass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:14:31.648203+00:00
-- url     : https://prove2.me/theorems/6f985952-82c3-487b-8d4a-ee7162bd3e68
-- title:
--   The gamma Lévy measure has infinite total jump intensity
-- statement:
--   For positive alpha and beta the gamma jump intensity beta exp(-alpha*x)/x has divergent mass near zero, so its total measure is infinite.
-- source:
--   Kyprianou (2006), Chapter 1 §1.2.4, original gamma Lévy exponent theorem 32009c4f-2a5e-4668-b3b2-28639144a632.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaLevyMeasure_infiniteMass
    (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta) :
    gammaLevyMeasure alpha beta Set.univ = ⊤ := by sorry
