-- Prove2me | Theorems.Thm_Kawahira_xi_eq_zero_iff_nontrivial
-- name    : Kawahira.xi_eq_zero_iff_nontrivial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T22:44:11.989674+00:00
-- url     : https://prove2.me/theorems/453890b4-67ed-47e2-b75b-b0601a5b3378
-- title:
--   Zeros of xi are exactly the nontrivial zeros of zeta
-- statement:
--   Away from the origin, Kawahira's normalized xi function vanishes exactly at the nontrivial zeros of the Riemann zeta function. In particular, the apparent Gamma singularities at the negative even integers introduce no xi zeros.
-- source:
--   Classical zero correspondence for the Riemann xi function, using its functional equation and the completed-zeta factorization.

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_nontrivial_zero_mem_strip
import Theorems.Thm_Kawahira_xi_one_sub

open Complex Topology

namespace Kawahira

theorem xi_eq_zero_iff_nontrivial (s : ℂ) (hs0 : s ≠ 0) :
    xi s = 0 ↔ IsNontrivialZero s := by sorry
