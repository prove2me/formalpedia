-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_inner_exp_lintegral_public
-- name    : Kyprianou.Ch08.StageB.p2m81_tail_kernel_inner_exp_lintegral_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T05:18:22.354501+00:00
-- url     : https://prove2.me/theorems/426bf966-1f53-4e67-9646-7a67f7373a2b
-- title:
--   Inner exponential lintegral over Ico (public)
-- statement:
--   For s>0 and any real z, the lower Lebesgue integral of exp(-s*y) over Ico 0 z equals (1-exp(-s*z))/s as an ENNReal number. Public bridge for the tail-kernel Tonelli inner integral.
-- source:
--   Public source-faithful duplicate of private helper Kyprianou.Ch08.StageB.p2m81_inner_exp_lintegral (f7138fd3-4403-4feb-a345-934fe8382169, candidate 45337 ACCEPTED) which cannot be imported by public parent 15634117-9988-4944-84fd-3d20bc3df5d3. Extracted from draft /tmp/p2m81_opt2.lean lines 121-156 with elaboration fixes from /tmp/f7138_repair7.lean (intervalIntegral.integral_of_le, integral_Ico_eq_integral_Ioc direction, integral_comp_mul_left args, div_eq_mul_inv zero case). Supplies hInner for the Tonelli swap in the excess Laplace identity.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_tail_kernel_inner_exp_lintegral_public
    (s : ℝ) (hs : 0 < s) (z : ℝ) :
    (∫⁻ y in Ico (0 : ℝ) z, ENNReal.ofReal (Real.exp (-s * y)) ∂volume) =
      (1 - ENNReal.ofReal (Real.exp (-s * z))) / ENNReal.ofReal s := by sorry
