-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaArrivalConvolutionPowerViaKernel
-- name    : Kyprianou.Ch01.gammaArrivalConvolutionPowerViaKernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T08:14:28.065255+00:00
-- url     : https://prove2.me/theorems/52ea09be-7319-4d61-bd78-f8cb186d5283
-- title:
--   Exponential increment convolution powers agree with gamma arrival-time measures
-- statement:
--   All positive convolution powers of the source exponential-increment measure equal the corresponding Erlang arrival-time measures. Prove by induction using source exponential to first gamma measure equality and a direct gamma convolution density kernel.
-- source:
--   Kyprianou (2006), Exercise 1.8(iv), worked solution pp.304–305

import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.WithDensity
import Definitions.Def_QueueingFundamentals_MG1_transforms
import Definitions.Def_levy_foundations_arrivalGammaDensity
open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch01.gammaArrivalConvolutionPowerViaKernel
    (beta : ℝ) (hbeta : 0 < beta) :
    let mu : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * x)))
    ∀ n : ℕ, QueueingFundamentals.MG1.convPow mu (n + 1) =
      volume.withDensity (LevyFoundations.arrivalGammaDensity beta n) := by
  sorry
