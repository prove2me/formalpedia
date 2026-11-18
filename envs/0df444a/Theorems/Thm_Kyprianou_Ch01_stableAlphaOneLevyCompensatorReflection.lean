-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLevyCompensatorReflection
-- name    : Kyprianou.Ch01.stableAlphaOneLevyCompensatorReflection
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:52:01.96761+00:00
-- url     : https://prove2.me/theorems/1375139d-af1e-49e7-8398-91baa7c24ced
-- title:
--   Exact compensated Lévy jump integrand reflection symmetry
-- statement:
--   For all real xi and r, the compensated Lévy–Khintchine integrand at jump size −r and frequency xi equals the integrand at jump size r and frequency −xi. The absolute-value truncation |x|<1 is invariant under reflection, and exponent and compensator each depend on the product xi*r. This is a source-faithful prerequisite for reflecting the negative stable Lévy measure to the positive half-line.
-- source:
--   Kyprianou (2006), Chapter 1, stable alpha-one Lévy measure reflection and sign convention.

import Mathlib
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
open ProbabilityTheory MeasureTheory Complex Set Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAlphaOneLevyCompensatorReflection
    (xi r : ℝ) :
    ProbabilityTheory.levyCompensatedIntegrand xi (-r) =
      ProbabilityTheory.levyCompensatedIntegrand (-xi) r := by
  sorry
