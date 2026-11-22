-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_f_closed_form_public
-- name    : Kyprianou.Ch08.StageB.p2m81_tail_kernel_f_closed_form_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T05:20:45.712747+00:00
-- url     : https://prove2.me/theorems/056c8127-8360-4417-b448-05abf5b814bf
-- title:
--   Tail-kernel f-closed form (public)
-- statement:
--   For s>0 with s≠d, the withDensity tail kernel Laplace value equals the closed f-formula (s*f d - d*f s)/(s*(f d - f s)) via the drawdown equation. Public bridge for the parent f-form leg.
-- source:
--   Public source-faithful extraction from public parent 15634117-9988-4944-84fd-3d20bc3df5d3 draft /tmp/p2m81_opt2.lean lines 196-218 (hEq1 via excess Laplace, hLρ_eq via hLle/hLne, hfd_ne, field_simp/linarith, ofReal algebra). Intended proof imports sibling excess_laplace_public for hFirst and proves hLle/hLne locally. Slim-bridge split required because 89-line single-import bridge scores -0.0080 above cutoff -0.0523; this leg plus gap leg reduce bridge to 27 lines / 9 tactics (score -1.24).

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_tail_kernel_f_closed_form_public
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (d : ℝ) (hd : 0 < d) (ρ : Measure ℝ)
    (hprob : IsProbabilityMeasure ρ)
    (hsupp : ρ (Iio (0 : ℝ)) = 0)
    (heq : ∀ s : ℝ, 0 < s →
      (f d - f s) * (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ).toReal =
        f d * (1 - s / d))
    (s : ℝ) (hs : 0 < s) (hne : s ≠ d) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂(volume.withDensity (fun y => if 0 ≤ y then ENNReal.ofReal d * ρ (Ioi y) else 0))) =
      ENNReal.ofReal ((s * f d - d * f s) / (s * (f d - f s))) := by sorry
