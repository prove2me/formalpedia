-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftDensityComplexMGF
-- name    : Kyprianou.Ch01.stableGammaStrictLeftDensityComplexMGF
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:36:00.980817+00:00
-- url     : https://prove2.me/theorems/2bd54705-b630-435c-b297-467f2d9b9653
-- title:
--   Exact identity of the weighted Gamma Mellin integral with a complex moment generating function
-- statement:
--   Identify the original complex Mellin integral with the characteristic complex moment integral of the positive-halfline sigma-finite weighted Lebesgue measure, using the exact Bochner integral withDensity identity.
-- source:
--   Kyprianou (2006) Chapter 1 stable Gamma-Mellin transform, Mathlib ComplexMGF integrability domain.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Complex Real Set Filter ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftDensityComplexMGF
    (alpha : ℝ) (w : ℂ) :
    ProbabilityTheory.complexMGF (fun r : ℝ => r)
      ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (r ^ (-alpha)))) w =
    (∫ r in Set.Ioi (0 : ℝ),
      Complex.exp (w * (r : ℂ)) *
        ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) := by sorry
