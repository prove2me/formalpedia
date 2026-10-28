-- Prove2me | Theorems.Thm_LL_Decomp1525c_thetaI_high
-- name    : LL_Decomp1525c.thetaI_high
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:04:50.132728+00:00
-- url     : https://prove2.me/theorems/06b06231-5f95-4fc4-b6bf-2348a4145b76
-- title:
--   Identify the upper interval prime sum
-- statement:
--   For real $x\ge6$ and $x\le u\le2x$, $I_x(u)=\max(\theta(\min(x-3,2x-u))-\log2,0)$, where $\theta$ is Chebyshev's prime logarithm sum.
-- source:
--   R. C. Vaughan, On the estimation of Schnirelman's constant, J. reine angew. Math. 290, 1977, pp. 93 to 108, p. 103, proof of Lemma 11. https://doi.org/10.1515/crll.1977.290.93

import Mathlib
import Definitions.Def_LL_Decomp1525c_P1V
import Definitions.Def_LL_Decomp1525c_thetaI
open Finset Real MeasureTheory intervalIntegral
open scoped Classical

namespace LL_Decomp1525c
theorem thetaI_high (x u : ℝ) (hx : 6 ≤ x) (hxu : x ≤ u) (hu : u ≤ 2 * x) :
    thetaI x u = max (Chebyshev.theta (min (x - 3) (2 * x - u)) - Real.log 2) 0 := by sorry
end LL_Decomp1525c
