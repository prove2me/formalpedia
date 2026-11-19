-- Prove2me | Theorems.Thm_Kyprianou_Ch01_expConvolutionPowerGammaDensity
-- name    : Kyprianou.Ch01.expConvolutionPowerGammaDensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T07:26:20.10225+00:00
-- url     : https://prove2.me/theorems/0b1002ab-f40c-4294-94ce-54bea484e1b0
-- title:
--   Each positive convolution power of the source exponential law is the Erlang arrival-density measure
-- statement:
--   The (n+1)-fold additive convolution of the exact source rate-beta exponential increment law equals the measure with Gamma/Erlang(n+1,beta) density LevyFoundations.arrivalGammaDensity beta n, for every n>=0. The base case is the source-to-arrival density equality, and the successor uses the independently Proved LevyFoundations gamma-density convolution theorem. This establishes a source-exact bridge into Kyprianou Exercise 1.8(iv).
-- source:
--   Kyprianou (2006), Exercise 1.8(iv), pp.304–305

import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.WithDensity
import Definitions.Def_QueueingFundamentals_MG1_transforms
import Definitions.Def_levy_foundations_arrivalGammaDensity
import Theorems.Thm_levy_foundations_arrivalGammaDensityConvolution
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.expConvolutionPowerGammaDensity
    (beta : ℝ) (hbeta : 0 < beta) :
    let mu : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal (beta * Real.exp (-beta * x)))
    ∀ n : ℕ, QueueingFundamentals.MG1.convPow mu (n + 1) =
      volume.withDensity (LevyFoundations.arrivalGammaDensity beta n) := by
  sorry
