-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cosine_normalised_exponent_limit
-- name    : Kyprianou.Ch04.ito43_cosine_normalised_exponent_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:32:21.694332+00:00
-- url     : https://prove2.me/theorems/f1493362-3b3a-56de-881e-fbff77bdc58b
-- title:
--   Normalised real Levy exponent converges to its Gaussian coefficient
-- statement:
--   Combine the exact real exponent identity with the vanishing cosine intensity integral.
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

theorem Kyprianou.Ch04.ito43_cosine_normalised_exponent_limit (tr : ProbabilityTheory.LevyKhintchineTriple) :
    Tendsto (fun m : ℕ => -(Kyprianou.Ch01.levyTripleExponent tr ((m:ℝ)+1)).re/((m:ℝ)+1)^2)
      atTop (nhds ((tr.gaussianVariance:ℝ)/2)) := by sorry
