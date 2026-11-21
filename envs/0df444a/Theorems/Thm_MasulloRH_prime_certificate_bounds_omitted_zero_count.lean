-- Prove2me | Theorems.Thm_MasulloRH_prime_certificate_bounds_omitted_zero_count
-- name    : MasulloRH.prime_certificate_bounds_omitted_zero_count
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:37:19.431186+00:00
-- url     : https://prove2.me/theorems/5ed7b6c5-32e9-425a-b640-b2b340bf26e9
-- title:
--   A finite prime certificate bounds the total multiplicity of omitted low zeros
-- statement:
--   Given a cutoff N+1 prime-comparison witness, every finite set of omitted zeros through height H has total multiplicity at most 384(1+H²)/N^(3/2). The bound applies jointly to all omitted zeros in the height window.
-- source:
--   https://prove2.me/theorems/609ef94c-0c43-4a17-9c98-af5a496118c2

import Theorems.Thm_MasulloRH_critical_line_certificate_bounds_missing_zero_mass
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Mathlib
open ArithmeticFunction MasulloRH

namespace MasulloRH
theorem prime_certificate_bounds_omitted_zero_count (N : ℕ) (hN : 1 ≤ N)
    (F : Finset (ZetaZerosInTraceStrip (1/2))) (hF : ∀ z ∈ F, z.val.re = 1/2)
    (hcert : Real.log 2/2 + Real.pi/4 - 37/30 +
      (∑ j ∈ Finset.range (N+1), (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))) ≤
      ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4))))
    (H : ℝ) (S : Finset (ZetaZerosInTraceStrip (1/2)))
    (hS : ∀ z ∈ S, z ∉ F ∧ |z.val.im| ≤ H) :
    (∑ z ∈ S, (analyticOrderNatAt riemannZeta z.val:ℝ)) * (N:ℝ)^(3/2:ℝ) ≤
      384*(1+H^2) := by sorry
end MasulloRH
