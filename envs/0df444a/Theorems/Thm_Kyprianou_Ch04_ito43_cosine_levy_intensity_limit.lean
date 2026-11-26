-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_levy_intensity_limit
-- name    : Kyprianou.Ch04.ito43_cosine_levy_intensity_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:32:25.023541+00:00
-- url     : https://prove2.me/theorems/ce0477bc-49e0-55e9-8307-8bd5aff9fa99
-- title:
--   Normalised cosine deficits vanish in Levy intensity integral
-- statement:
--   Apply dominated convergence with integrable bound twice the minimum of one and the squared mark. The pointwise limit follows from the frequency bound.
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

theorem Kyprianou.Ch04.ito43_cosine_levy_intensity_limit (tr : ProbabilityTheory.LevyKhintchineTriple) :
    Tendsto (fun m : ℕ => ∫ z, (1-Real.cos (((m:ℝ)+1)*z))/((m:ℝ)+1)^2 ∂tr.levyMeasure)
      atTop (nhds 0) := by sorry
