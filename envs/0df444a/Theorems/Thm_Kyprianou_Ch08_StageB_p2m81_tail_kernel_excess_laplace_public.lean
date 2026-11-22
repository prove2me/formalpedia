-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_excess_laplace_public
-- name    : Kyprianou.Ch08.StageB.p2m81_tail_kernel_excess_laplace_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T05:18:22.282586+00:00
-- url     : https://prove2.me/theorems/8dfa4eb3-170f-4f60-8c14-dc98cd0c6218
-- title:
--   Excess tail-kernel Laplace identity (public)
-- statement:
--   The withDensity tail kernel with density d times rho((y,infty)) on y>=0 has Laplace transform d*(1-L_rho(s))/s for every s>0. Public bridge supplying the main Laplace leg of the tail-kernel parent.
-- source:
--   Public source-faithful extraction from public parent 15634117-9988-4944-84fd-3d20bc3df5d3 draft /tmp/p2m81_opt2.lean lines 42-81 (withDensity to Ici integral, pull d, tail as inner integral) plus 118-120/157-188 (Tonelli, inner, outer, tsub). Intended proof imports the three sibling public bridges inner/swap/tsub; density term byte-identical to parent bridge construction. Supplies hFirst for the parent bridge.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_tail_kernel_excess_laplace_public
    (d : ℝ) (ρ : Measure ℝ)
    (hprob : IsProbabilityMeasure ρ)
    (hsupp : ρ (Iio (0 : ℝ)) = 0)
    (s : ℝ) (hs : 0 < s) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂(volume.withDensity (fun y => if 0 ≤ y then ENNReal.ofReal d * ρ (Ioi y) else 0))) =
      ENNReal.ofReal d * (1 - (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ)) / ENNReal.ofReal s := by sorry
