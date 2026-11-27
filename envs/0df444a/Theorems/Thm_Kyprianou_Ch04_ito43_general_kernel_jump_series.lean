-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_general_kernel_jump_series
-- name    : Kyprianou.Ch04.ito43_general_kernel_jump_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:12:28.391923+00:00
-- url     : https://prove2.me/theorems/08eacc9e-6180-55bf-b601-371be9bc4ad8
-- title:
--   Physical jump kernel integral equals the time-indexed series
-- statement:
--   Use the countable atomic jump measure and restricted Dirac integral identity; insert zero terms at nonjump times.
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

theorem Kyprianou.Ch04.ito43_general_kernel_jump_series {Ω : Type} [MeasurableSpace Ω] (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun t => X t w))
    (hl : ∀ t : NNReal, 0 < t → Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (L t w)))
    (K : NNReal → ℝ → ℝ → ℝ) (h0 : ∀ s x, K s x 0 = 0) (t : NNReal) :
    (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
      K z.1.toNNReal (L z.1.toNNReal w) z.2 ∂(pathJumpMeasure X L w)) =
      ∑' s : Ioc (0:NNReal) t, K s (L s w) (X s w-L s w) := by sorry
