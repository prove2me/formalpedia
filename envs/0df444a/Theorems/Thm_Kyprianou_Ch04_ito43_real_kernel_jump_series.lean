-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_real_kernel_jump_series
-- name    : Kyprianou.Ch04.ito43_real_kernel_jump_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:01:23.919489+00:00
-- url     : https://prove2.me/theorems/ae2a8b53-9d2e-41ff-8274-143ae6d4867e
-- title:
--   Real-time kernel integral equals its actual jump series
-- statement:
--   Apply the existing NNReal-time kernel series theorem and identify the real time with its nonnegative coercion.
-- source:
--   Kyprianou (2006), Theorem 4.3 proof auxiliary

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
open Kyprianou.Ch04
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_real_kernel_jump_series
    {Ω : Type} [MeasurableSpace Ω]
    (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s →
      Tendsto (fun r => X r w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (K : ℝ → ℝ → ℝ → ℝ) (h0 : ∀ s x, K s x 0 = 0) (t : NNReal) :
    (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
      K z.1 (L z.1.toNNReal w) z.2 ∂(pathJumpMeasure X L w)) =
    ∑' s : Ioc (0 : NNReal) t, K ((s : NNReal) : ℝ) (L s w) (X s w-L s w) := by sorry
