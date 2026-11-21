-- Prove2me | Theorems.Thm_MasulloRH_critical_line_certificate_bounds_missing_zero_mass
-- name    : MasulloRH.critical_line_certificate_bounds_missing_zero_mass
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:55:36.4325+00:00
-- url     : https://prove2.me/theorems/609ef94c-0c43-4a17-9c98-af5a496118c2
-- title:
--   A finite prime–critical-line certificate bounds all omitted zeros and certifies a zero-free band off the line
-- statement:
--   Suppose a finite set $F$ of critical-line zeros passes the reference-mass comparison using all prime powers through $N\ge1$. Then $$\sum_{\rho\notin F}\frac{m(\rho)}{1+(\Im\rho)^2}\le\frac{384}{N^{3/2}}.$$ In particular, every omitted zero satisfies $m(\rho)N^{3/2}\le384(1+(\Im\rho)^2)$. Hence all zeros with $384(1+|\Im\rho|^2)<N^{3/2}$ must occur in $F$. Conversely, an off-line zero of ordinate $\gamma$ forces failure at every prime cutoff with $N^{3/2}>384(1+\gamma^2)$.
-- source:
--   Effective converse to the rational prime–critical-line-mass criterion (bd574b97). Uses the full-strip regularized trace, positivity of the reference resolvent, and dyadic Chebyshev estimates for the von Mangoldt tail.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option autoImplicit false

open Finset ArithmeticFunction
namespace MasulloRH

theorem critical_line_certificate_bounds_missing_zero_mass (N : ℕ) (hN : 1 ≤ N)
    (F : Finset (ZetaZerosInTraceStrip (1/2))) (hF : ∀ z ∈ F, z.val.re = 1/2)
    (hcert : Real.log 2/2 + Real.pi/4 - 37/30 +
      (∑ j ∈ Finset.range (N+1), (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))) ≤
      ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))) :
    (∑' z : ZetaZerosInTraceStrip (1/2), if z ∈ F then 0 else zeroDecayWeight (1/2) z)
         ≤ 384/(N:ℝ)^(3/2:ℝ) ∧
    ∀ z : ZetaZerosInTraceStrip (1/2), z ∉ F →
      (analyticOrderNatAt riemannZeta z.val:ℝ)*(N:ℝ)^(3/2:ℝ) ≤ 384*(1+z.val.im^2) := by sorry

end MasulloRH
