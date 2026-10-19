-- Prove2me | Theorems.Thm_MazurTransfer_Order13ReflectionParameter_transcendental_reflectionX
-- name    : MazurTransfer.Order13ReflectionParameter.transcendental_reflectionX
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T21:10:16.247961+00:00
-- url     : https://prove2.me/theorems/1b9206e6-6723-431a-ad48-1fdcfbdea965
-- title:
--   The original fractional-linear reflection preserves transcendence
-- statement:
--   For the original field extension and every transcendental coordinate, the original fractional-linear reflection remains transcendental under exactly the original nonzero scalar hypothesis. Both field universes and every original algebra and denominator-related hypothesis are retained.
-- source:
--   MazurTheorem Order13ReflectionParameter.transcendental_reflectionX; complete original telescope and all universe parameters retained; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ReflectionCoordinatesAndParameterOriginalDataSingleUniverseBlockV220261018
noncomputable section
universe u v
open MazurTransfer.Order13ReflectionSexticSymmetry MazurTransfer.Order13ReflectionParameter Polynomial

theorem MazurTransfer.Order13ReflectionParameter.transcendental_reflectionX {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] (t : K) (x : F)
    (hD : reflectionScalar (algebraMap K F t) ≠ 0)
    (hx : Transcendental K x) : Transcendental K (reflectionX (algebraMap K F t) x) := by sorry
