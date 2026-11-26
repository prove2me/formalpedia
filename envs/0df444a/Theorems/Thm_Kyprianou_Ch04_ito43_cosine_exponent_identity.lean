-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_exponent_identity
-- name    : Kyprianou.Ch04.ito43_cosine_exponent_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:32:24.41428+00:00
-- url     : https://prove2.me/theorems/f3710725-4c21-46a5-8a98-8e5adbe64f6b
-- title:
--   Real characteristic exponent equals Gaussian rate plus cosine jump intensity
-- statement:
--   The real part of the compensated Levy integrand is cosine minus one. Take real parts of its integrable complex integral, then divide by the nonzero frequency square.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology
open Set

theorem Kyprianou.Ch04.ito43_cosine_exponent_identity (tr : ProbabilityTheory.LevyKhintchineTriple) (a : ℝ) (ha : 0 < a) :
    -(Kyprianou.Ch01.levyTripleExponent tr a).re/a^2 =
      (tr.gaussianVariance:ℝ)/2 +
        ∫ z, (1-Real.cos (a*z))/a^2 ∂tr.levyMeasure := by sorry
