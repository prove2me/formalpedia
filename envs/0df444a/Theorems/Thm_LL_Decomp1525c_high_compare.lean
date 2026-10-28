-- Prove2me | Theorems.Thm_LL_Decomp1525c_high_compare
-- name    : LL_Decomp1525c.high_compare
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:08:17.809114+00:00
-- url     : https://prove2.me/theorems/5422362f-b419-4f77-8fd8-50102cd0e87e
-- title:
--   Compare the upper integrals
-- statement:
--   Assume $|\theta(y)-y|<y/(40\log y)$ for every real $y\ge678407$, where $\theta$ is Chebyshev's prime logarithm sum. For every real $x\ge10^{52}$, $|\int_x^{2x}I_x(u)/\log u\,du-\int_x^{2x}(2x-u)/\log u\,du|\le x^2/(20\log^2x)$.
-- source:
--   R. C. Vaughan, On the estimation of Schnirelman's constant, J. reine angew. Math. 290, 1977, pp. 93 to 108, p. 103, proof of Lemma 11. https://doi.org/10.1515/crll.1977.290.93

import Mathlib
import Definitions.Def_LL_Decomp1525c_P1V
import Definitions.Def_LL_Decomp1525c_thetaI
open Finset Real MeasureTheory intervalIntegral
open scoped Classical

namespace LL_Decomp1525c
theorem high_compare
    (h215 : ∀ y : ℝ, 678407 ≤ y → |Chebyshev.theta y - y| < y / (40 * Real.log y))
    (x : ℝ) (hx : 10 ^ 52 ≤ x) :
    |(∫ u in x..(2 * x), thetaI x u / Real.log u) - ∫ u in x..(2 * x), (2 * x - u) / Real.log u|
      ≤ x ^ 2 / (20 * Real.log x ^ 2) := by sorry
end LL_Decomp1525c
