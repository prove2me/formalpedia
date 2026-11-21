-- Prove2me | Theorems.Thm_GRH_signed_square_block_moebius_means_below_boundary
-- name    : GRH.signed_square_block_moebius_means_below_boundary
-- status  : Open
-- author  : @marozols
-- created : 2026-11-21T02:23:48.611084+00:00
-- url     : https://prove2.me/theorems/b1b42fc9-559d-4868-af9e-3e850ec21ab9
-- title:
--   Signed averages of centered Möbius errors between consecutive squares in the remaining exponent range
-- statement:
--   Fix a positive modulus q, a reduced class a, and 1/2<σ≤0.8749570698. On each complete interval [u²,(u+1)²), take the signed arithmetic mean of the centered Möbius progression bilinear errors. The proposed open estimate is |mean|≤C(q,a,σ)(u²+1)^σ uniformly in u. Only one signed mean per square interval is prescribed, with every divisor cutoff fixed at u throughout the average. This leaves cancellation inside the average available. The comparison with the entire sharp frontier uses the unconditional O_q(√N+1) variation theorem.
-- source:
--   Proposed remaining arithmetic input for GRH.centered_moebius_progression_bilinear_power_bound (5000f709), based on the finite truncation in Helfgott–Thompson §2, https://doi.org/10.1007/s40993-022-00408-8. The source supplies the truncation. The signed square-block cancellation bound remains open.

import Definitions.Def_GRH_MoebiusBilinear

set_option autoImplicit false

open Finset
namespace GRH

theorem signed_square_block_moebius_means_below_boundary (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (σ : ℝ) (hhalf : 1/2 < σ) (hcap : σ ≤ 0.8749570698) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ,
      |(∑ j ∈ range (2*u+1), centeredMoebiusBilinear q a (u^2+j))/((2*u+1:ℕ):ℝ)| ≤
        C*((u:ℝ)^2+1)^σ := by sorry

end GRH
