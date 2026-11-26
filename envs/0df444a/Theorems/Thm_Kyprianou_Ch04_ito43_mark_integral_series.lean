-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_mark_integral_series
-- name    : Kyprianou.Ch04.ito43_mark_integral_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T20:21:44.757802+00:00
-- url     : https://prove2.me/theorems/fca38256-765c-4d62-b8b5-2f3ccdb9e2d4
-- title:
--   A mark-only jump integral equals the physical jump series
-- statement:
--   Use the proved countability and atomic Dirac representation. Reindex the restricted sum over positive times, inserting zero-valued marks where the jump vanishes.
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

theorem Kyprianou.Ch04.ito43_mark_integral_series {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun t => X t w))
    (hl : ∀ t : NNReal, 0 < t → Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (r : ℝ → ℝ) (h0 : r 0 = 0) (t : NNReal) :
    (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ), r z.2 ∂(pathJumpMeasure X L w)) =
      ∑' s : Ioc (0:NNReal) t, r (X s w-L s w) := by sorry
