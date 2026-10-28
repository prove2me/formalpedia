-- Prove2me | Theorems.Thm_LL_Decomp1525c_low_pointwise
-- name    : LL_Decomp1525c.low_pointwise
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:05:40.85617+00:00
-- url     : https://prove2.me/theorems/b3bbb963-49d8-4249-a298-f349ca914ba7
-- title:
--   Bound the lower interval pointwise error
-- statement:
--   Assume $|\theta(y)-y|<y/(40\log y)$ for every real $y\ge678407$, where $\theta$ is Chebyshev's prime logarithm sum. For real $x\ge10^{52}$ and $3\le u\le x$, with $t=\max(x-u,2)$, $|I_x(u)-u|\le x/(40\log x)+t/(40\log t)+678412$.
-- source:
--   R. C. Vaughan, On the estimation of Schnirelman's constant, J. reine angew. Math. 290, 1977, pp. 93 to 108, p. 103, proof of Lemma 11. https://doi.org/10.1515/crll.1977.290.93

import Mathlib
import Definitions.Def_LL_Decomp1525c_P1V
import Definitions.Def_LL_Decomp1525c_thetaI
open Finset Real MeasureTheory intervalIntegral
open scoped Classical

namespace LL_Decomp1525c
theorem low_pointwise
    (h215 : ∀ y : ℝ, 678407 ≤ y → |Chebyshev.theta y - y| < y / (40 * Real.log y))
    (x u : ℝ) (hx : 10 ^ 52 ≤ x) (hu3 : 3 ≤ u) (hux : u ≤ x) :
    |thetaI x u - u| ≤ x / (40 * Real.log x)
      + max (x - u) 2 / (40 * Real.log (max (x - u) 2)) + 678412 := by sorry
end LL_Decomp1525c
