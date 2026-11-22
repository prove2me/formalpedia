-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_laplace_tsub_public
-- name    : Kyprianou.Ch08.StageB.p2m81_tail_kernel_laplace_tsub_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T05:18:21.916912+00:00
-- url     : https://prove2.me/theorems/4de86d16-b27f-492d-a70d-da37b8ad7b50
-- title:
--   Laplace tsub split over supported rho (public)
-- statement:
--   For s>0 and a probability measure rho supported on [0,infty), the lower integral of (1-exp(-s*z)) splits as one minus the Laplace transform of rho. Public bridge for the tail-kernel outer integral.
-- source:
--   Public source-faithful extraction from public parent 15634117-9988-4944-84fd-3d20bc3df5d3 draft /tmp/p2m81_opt2.lean lines 31-40 (hLle support bound) and 164-187 (hF_add_ae, lintegral_add split, ENNReal.add_sub_cancel_left). Needs hsupp for the a.e. exp<=1 bound. Supplies hSubEq for the excess Laplace identity.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_tail_kernel_laplace_tsub_public
    (s : ℝ) (hs : 0 < s) (ρ : Measure ℝ)
    (hprob : IsProbabilityMeasure ρ)
    (hsupp : ρ (Iio (0 : ℝ)) = 0) :
    (∫⁻ z, (1 - ENNReal.ofReal (Real.exp (-s * z))) ∂ρ) =
      1 - ∫⁻ z, ENNReal.ofReal (Real.exp (-s * z)) ∂ρ := by sorry
