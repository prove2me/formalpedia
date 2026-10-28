-- Prove2me | Theorems.Thm_LL_Decomp1525c_thetaI_low
-- name    : LL_Decomp1525c.thetaI_low
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:04:11.345716+00:00
-- url     : https://prove2.me/theorems/08e8ddbb-7f57-43ae-8e1a-a38f1166c761
-- title:
--   Identify the lower interval prime sum
-- statement:
--   For real $x\ge6$ and $3\le u\le x$, $I_x(u)=\theta(x-3)-\theta(\max(x-u,2))$, where $\theta(t)=\sum_{p\le t}\log p$ over primes.
-- source:
--   R. C. Vaughan, On the estimation of Schnirelman's constant, J. reine angew. Math. 290, 1977, pp. 93 to 108, p. 103, proof of Lemma 11. https://doi.org/10.1515/crll.1977.290.93

import Mathlib
import Definitions.Def_LL_Decomp1525c_P1V
import Definitions.Def_LL_Decomp1525c_thetaI
open Finset Real MeasureTheory intervalIntegral
open scoped Classical

namespace LL_Decomp1525c
theorem thetaI_low (x u : ℝ) (hx : 6 ≤ x) (hu3 : 3 ≤ u) (hux : u ≤ x) :
    thetaI x u = Chebyshev.theta (x - 3) - Chebyshev.theta (max (x - u) 2) := by sorry
end LL_Decomp1525c
