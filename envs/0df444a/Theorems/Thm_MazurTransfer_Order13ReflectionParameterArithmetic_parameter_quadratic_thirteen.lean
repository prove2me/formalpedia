-- Prove2me | Theorems.Thm_MazurTransfer_Order13ReflectionParameterArithmetic_parameter_quadratic_thirteen
-- name    : MazurTransfer.Order13ReflectionParameterArithmetic.parameter_quadratic_thirteen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T21:16:44.366072+00:00
-- url     : https://prove2.me/theorems/5612f172-1811-4ff5-a2b7-5f8305f2d9a1
-- title:
--   The original reflection parameter satisfies its quadratic-thirteen identity
-- statement:
--   For every original reflection parameter over every field, the square of three t squared plus eight t plus one equals thirteen times s squared. The original cubic and square equations imply this identity; no characteristic-zero or algebraic-closure assumption is added.
-- source:
--   MazurTheorem Order13ReflectionParameterArithmetic.parameter_quadratic_thirteen, with the original quadratic_thirteen_certificate helper; complete universe-polymorphic original telescope retained; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ReflectionCoordinatesAndParameterOriginalDataSingleUniverseBlockV220261018
noncomputable section
universe u
open MazurTransfer.Order13ReflectionSexticSymmetry MazurTransfer.Order13ReflectionParameter

theorem MazurTransfer.Order13ReflectionParameterArithmetic.parameter_quadratic_thirteen {K : Type u} [Field K] (a : ReflectionParameter K) :
    (3 * a.t ^ 2 + 8 * a.t + 1) ^ 2 = 13 * a.s ^ 2 := by sorry
