-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_tonelli_lhs_public
-- name    : Kyprianou.Ch08.StageB.p2m81_tail_kernel_tonelli_lhs_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T05:23:47.825774+00:00
-- url     : https://prove2.me/theorems/b872c03c-d8a1-4e2f-ae3a-cb05fdb9aa22
-- title:
--   Tonelli LHS indicator collapse (public)
-- statement:
--   The uncurried if-indicator double integral collapses on the y-side to the Ici-restricted iterated integral over Ioi y. Public leaf for the Tonelli swap.
-- source:
--   Public source-faithful extraction from parent 15634117 draft /tmp/p2m81_opt2.lean lines 86-106 (hLHS_id indicator algebra + hLHS_swap). Gate split required: full 42-line Tonelli swap scores +0.114 above cutoff (cyclomatic 11 from repeated ifs); this 24-line LHS leaf scores -0.40. Proof draft /tmp/tailgap_c2a1_proof_draft.lean. Supplies LHS leg for tonelli_swap_public combiner.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_tail_kernel_tonelli_lhs_public
    (s : ℝ) (ρ : Measure ℝ) (hprob : IsProbabilityMeasure ρ) :
    (∫⁻ y, ∫⁻ z, (if 0 ≤ y ∧ y < z then ENNReal.ofReal (Real.exp (-s * y)) else 0) ∂ρ ∂volume) =
      ∫⁻ y in Ici (0 : ℝ), (∫⁻ z in Ioi y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ∂volume := by sorry
