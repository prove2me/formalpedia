-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_tonelli_swap_public
-- name    : Kyprianou.Ch08.StageB.p2m81_tail_kernel_tonelli_swap_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T05:18:25.459052+00:00
-- url     : https://prove2.me/theorems/16389c99-bb2d-47a1-a022-2e8fe3832612
-- title:
--   Tail-kernel Tonelli swap (public)
-- statement:
--   For any real s and probability measure rho on the line, the iterated lower integral of exp(-s*y) over y>=0 and z>y swaps to the iterated integral over z and y in Ico 0 z. Public bridge for the tail-kernel Laplace computation.
-- source:
--   Public source-faithful extraction from public parent Kyprianou.Ch08.StageB.p2m81_tail_kernel_laplace_gap (15634117-9988-4944-84fd-3d20bc3df5d3) draft /tmp/p2m81_opt2.lean lines 82-120 (hUncMeas, lintegral_lintegral_swap, indicator algebra hLHS_id/hRHS_id). No support hypothesis needed; measurability plus Tonelli only. Supplies hTonelli for the excess Laplace identity.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_tail_kernel_tonelli_swap_public
    (s : ℝ) (ρ : Measure ℝ) (hprob : IsProbabilityMeasure ρ) :
    (∫⁻ y in Ici (0 : ℝ), (∫⁻ z in Ioi y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ∂volume) =
      ∫⁻ z, (∫⁻ y in Ico (0 : ℝ) z, ENNReal.ofReal (Real.exp (-s * y)) ∂volume) ∂ρ := by sorry
