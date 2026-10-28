-- Prove2me | Theorems.Thm_LL_Decomp1525c_high_pointwise
-- name    : LL_Decomp1525c.high_pointwise
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:06:26.80142+00:00
-- url     : https://prove2.me/theorems/d460f66f-20c4-458e-8273-1f6c5734579a
-- title:
--   Bound the upper interval pointwise error
-- statement:
--   Assume $|\theta(y)-y|<y/(40\log y)$ for every real $y\ge678407$, where $\theta$ is Chebyshev's prime logarithm sum. For real $x\ge10^{52}$ and $x\le u\le2x$, with $s=\max(\min(x-3,2x-u),2)$, $|I_x(u)-(2x-u)|\le s/(40\log s)+678412$.
-- source:
--   R. C. Vaughan, On the estimation of Schnirelman's constant, J. reine angew. Math. 290, 1977, pp. 93 to 108, p. 103, proof of Lemma 11. https://doi.org/10.1515/crll.1977.290.93

import Mathlib
import Definitions.Def_LL_Decomp1525c_P1V
import Definitions.Def_LL_Decomp1525c_thetaI
open Finset Real MeasureTheory intervalIntegral
open scoped Classical

namespace LL_Decomp1525c
theorem high_pointwise
    (h215 : ∀ y : ℝ, 678407 ≤ y → |Chebyshev.theta y - y| < y / (40 * Real.log y))
    (x u : ℝ) (hx : 10 ^ 52 ≤ x) (hxu : x ≤ u) (hu : u ≤ 2 * x) :
    |thetaI x u - (2 * x - u)| ≤
      max (min (x - 3) (2 * x - u)) 2 / (40 * Real.log (max (min (x - 3) (2 * x - u)) 2))
        + 678412 := by sorry
end LL_Decomp1525c
