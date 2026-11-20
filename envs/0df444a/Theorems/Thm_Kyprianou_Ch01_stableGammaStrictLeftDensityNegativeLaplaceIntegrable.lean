-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftDensityNegativeLaplaceIntegrable
-- name    : Kyprianou.Ch01.stableGammaStrictLeftDensityNegativeLaplaceIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:36:08.702571+00:00
-- url     : https://prove2.me/theorems/c84581a0-d587-4466-a6c3-6dc5ad3e728e
-- title:
--   All negative real exponential moments of the Gamma-weighted positive-halfline measure exist
-- statement:
--   Transfer the Gamma exponential envelope integrability from Lebesgue restricted to the positive halfline to the corresponding withDensity weighted measure. This is the exact exponential moment domain premise for ComplexMGF analyticity.
-- source:
--   Kyprianou (2006) Chapter 1 stable Gamma-Mellin transform, Mathlib ComplexMGF integrability domain.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Complex Real Set Filter ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftDensityNegativeLaplaceIntegrable
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (t : ℝ) (ht : t < 0) :
    Integrable (fun r : ℝ => Real.exp (t * r))
      ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (r ^ (-alpha)))) := by sorry
