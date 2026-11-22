-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_gap_point_public
-- name    : Kyprianou.Ch08.StageB.p2m81_tail_kernel_gap_point_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T05:20:42.459293+00:00
-- url     : https://prove2.me/theorems/17be22e6-b34e-43c4-b8b8-36e3460762ce
-- title:
--   Tail-kernel strict gap point (public)
-- statement:
--   The withDensity tail kernel Laplace value sits strictly below one at s0=d+1, using only the excess Laplace identity and d/(d+1)<1. Public bridge for the parent gap leg.
-- source:
--   Public source-faithful extraction from public parent 15634117-9988-4944-84fd-3d20bc3df5d3 draft /tmp/p2m81_opt2.lean lines 219-234 (s0=d+1, tsub_le_self, mul_le_mul_left/right, ofReal_div, ofReal_lt_one). Intended proof imports sibling excess_laplace_public for hFirst; no f/heq needed. Slim-bridge split required because 89-line single-import bridge is complexity-blocked; this leg plus f-form leg reduce bridge to gate-passing size.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_tail_kernel_gap_point_public
    (d : ℝ) (hd : 0 < d) (ρ : Measure ℝ)
    (hprob : IsProbabilityMeasure ρ)
    (hsupp : ρ (Iio (0 : ℝ)) = 0) :
    ∃ s0 : ℝ, 0 < s0 ∧
      (∫⁻ y, ENNReal.ofReal (Real.exp (-s0 * y)) ∂(volume.withDensity (fun y => if 0 ≤ y then ENNReal.ofReal d * ρ (Ioi y) else 0))) < 1 := by sorry
