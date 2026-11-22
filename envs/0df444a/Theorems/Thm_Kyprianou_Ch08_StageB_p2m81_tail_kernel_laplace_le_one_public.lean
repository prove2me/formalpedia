-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_tail_kernel_laplace_le_one_public
-- name    : Kyprianou.Ch08.StageB.p2m81_tail_kernel_laplace_le_one_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T05:23:49.237614+00:00
-- url     : https://prove2.me/theorems/d36d1c5b-e38e-4b37-b004-dbd32b1f1bda
-- title:
--   Supported Laplace bounded by one (public)
-- statement:
--   For s>0 and probability rho supported on [0,infty), the Laplace lower integral is at most one. Public leaf for tsub and f-form legs.
-- source:
--   Public extraction from parent 15634117 draft /tmp/p2m81_opt2.lean lines 31-40 (hLle via hae_nonneg + lintegral_mono_ae). Gate split required: full 45-line tsub scores +0.02 (37 tactics); this 17-line leaf scores -0.72, revised tsub importing it scores -0.12. Proof draft /tmp/tailgap_c2b1_proof_draft.lean. Supplies hLle for laplace_tsub_public and f_closed_form_public.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_tail_kernel_laplace_le_one_public
    (s : ℝ) (hs : 0 < s) (ρ : Measure ℝ)
    (hprob : IsProbabilityMeasure ρ)
    (hsupp : ρ (Iio (0 : ℝ)) = 0) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ρ) ≤ 1 := by sorry
