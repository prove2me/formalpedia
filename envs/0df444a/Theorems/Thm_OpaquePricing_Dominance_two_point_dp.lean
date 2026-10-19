-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_two_point_dp
-- name    : OpaquePricing.Dominance.two_point_dp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:58.412375+00:00
-- url     : https://prove2.me/theorems/09e4dc12-87e9-4234-9f8c-c7b33bd4059d
-- title:
--   Proof of Theorem 1, Case (ii): three candidate DP price vectors
-- statement:
--   Suppose $N\ge2$, $0\le a<b$, and an exchangeable valuation law is supported on $\{a,b\}^N$. Discriminatory pricing attains its optimal expected revenue at one of three price vectors: all prices $a$, all prices $b$, or exactly one price $a$ and all remaining prices $b$. Thus
--
--   $$R_{\mathrm{DP}}=\max\{R_{\mathrm{DP}}(a,\ldots,a),R_{\mathrm{DP}}(b,\ldots,b),R_{\mathrm{DP}}(a,b,\ldots,b)\}.$$
--
--   This reduces the two-value branch to three pricing patterns.
--
--   **Formalization Note** The low price in the mixed vector is at coordinate zero; exchangeability makes its location immaterial.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), proof of Theorem 1, Case (ii), p. 19

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OpaquePricing.Dominance

theorem two_point_dp {N : ℕ} (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hsupp : ∀ᵐ v ∂μ, ∀ i, v i = a ∨ v i = b)
    (hexch : Exchangeable μ) :
    optDP μ = max (expDP μ (fun _ => a))
      (max (expDP μ (fun _ => b)) (expDP μ (mixedPrice a b))) := by sorry

end OpaquePricing.Dominance
