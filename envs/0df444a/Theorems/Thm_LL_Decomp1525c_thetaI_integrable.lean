-- Prove2me | Theorems.Thm_LL_Decomp1525c_thetaI_integrable
-- name    : LL_Decomp1525c.thetaI_integrable
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-10-28T17:07:15.547926+00:00
-- url     : https://prove2.me/theorems/78f2877e-e7e2-4ac7-a46e-4ec13ad1e9e9
-- title:
--   Establish interval integrability
-- statement:
--   For every real $x\ge6$, the function $u\mapsto I_x(u)/\log u$ is interval integrable with respect to Lebesgue measure on both $[3,x]$ and $[x,2x]$.
-- source:
--   R. C. Vaughan, On the estimation of Schnirelman's constant, J. reine angew. Math. 290, 1977, pp. 93 to 108, p. 103, proof of Lemma 11. https://doi.org/10.1515/crll.1977.290.93

import Mathlib
import Definitions.Def_LL_Decomp1525c_P1V
import Definitions.Def_LL_Decomp1525c_thetaI
open Finset Real MeasureTheory intervalIntegral
open scoped Classical

namespace LL_Decomp1525c
theorem thetaI_integrable (x : ℝ) (hx : 6 ≤ x) :
    IntervalIntegrable (fun u => thetaI x u / Real.log u) volume 3 x ∧
    IntervalIntegrable (fun u => thetaI x u / Real.log u) volume x (2 * x) := by sorry
end LL_Decomp1525c
