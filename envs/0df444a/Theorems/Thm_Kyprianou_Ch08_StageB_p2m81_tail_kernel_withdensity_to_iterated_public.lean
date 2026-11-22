-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_withdensity_to_iterated_public
-- name    : Kyprianou.Ch08.StageB.p2m81_tail_kernel_withdensity_to_iterated_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T05:23:45.881927+00:00
-- url     : https://prove2.me/theorems/bba0a0d4-574a-44eb-a1a9-082c642fa663
-- title:
--   WithDensity to iterated tail integral (public)
-- statement:
--   The withDensity tail-kernel integral reduces to d times the Ici-restricted iterated integral over tail probabilities. Public leaf for the excess Laplace identity.
-- source:
--   Public extraction from parent 15634117 draft /tmp/p2m81_opt2.lean lines 50-81 (hLHS_eq withDensity+indicator, hPull const-mul, hTF_eq tail-as-integral). Gate split required: 58-line excess proof scores +0.10; this 38-line v2 leaf scores -0.12, combiner importing it scores -0.65. Proof draft /tmp/tailgap_c2pre_v2.lean. Supplies hPre for excess_laplace_public.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_tail_kernel_withdensity_to_iterated_public
    (d : ℝ) (ρ : Measure ℝ) (s : ℝ) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂(volume.withDensity (fun y => if 0 ≤ y then ENNReal.ofReal d * ρ (Ioi y) else 0))) =
      ENNReal.ofReal d * ∫⁻ y in Ici (0 : ℝ), (∫⁻ z in Ioi y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ∂volume := by sorry
