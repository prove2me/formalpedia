-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_tonelli_rhs_ptwise_public
-- name    : Kyprianou.Ch08.StageB.p2m81_tail_kernel_tonelli_rhs_ptwise_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T05:23:45.921411+00:00
-- url     : https://prove2.me/theorems/5c993cb2-1e28-4359-a89d-7b195e80bbd4
-- title:
--   Tonelli RHS pointwise indicator (public)
-- statement:
--   For fixed z, the y-integral of the if-indicator equals the Ico 0 z restricted integral. Public leaf for the Tonelli swap RHS.
-- source:
--   Public extraction from parent 15634117 draft /tmp/p2m81_opt2.lean lines 107-116 (hRHS_id). 11-line leaf scores -1.03. Proof draft /tmp/tailgap_c2a2_proof_draft.lean. Supplies pointwise RHS leg for tonelli_swap_public.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_tail_kernel_tonelli_rhs_ptwise_public
    (s : ℝ) (z : ℝ) :
    (∫⁻ y, (if 0 ≤ y ∧ y < z then ENNReal.ofReal (Real.exp (-s * y)) else 0) ∂volume) =
      ∫⁻ y in Ico (0 : ℝ) z, ENNReal.ofReal (Real.exp (-s * y)) ∂volume := by sorry
