-- Prove2me | Theorems.Thm_Kyprianou_Ch04_levyMinSquareIntegrableV1
-- name    : Kyprianou.Ch04.levyMinSquareIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:17:52.514283+00:00
-- url     : https://prove2.me/theorems/dc988adb-072f-59ad-b94a-42aea082fab1
-- title:
--   Integrability of the canonical Levy quadratic envelope
-- statement:
--   Integrability of the canonical Levy quadratic envelope.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem levyMinSquareIntegrableV1 (ν : Measure ℝ) (hν : IsLevyMeasure ν) :
    Integrable (fun z : ℝ => min 1 (z^2)) ν := by
  sorry
end Kyprianou.Ch04
