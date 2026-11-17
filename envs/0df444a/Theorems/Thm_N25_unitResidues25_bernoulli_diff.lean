-- Prove2me | Theorems.Thm_N25_unitResidues25_bernoulli_diff
-- name    : N25.unitResidues25_bernoulli_diff
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:59.309212+00:00
-- url     : https://prove2.me/theorems/5aba5d3d-de44-47ae-985e-50297ea8c4ae
-- title:
--   The Bernoulli difference equals the prescribed q-order
-- statement:
--   Let $i∈ℤ/5ℤ$, write $(r_{i,1},r_{i,2})$ for its residue pair, and put $B_2(x)=x^2-x+1/6$. If $q_i$ is the prescribed order of the $i$th unit, then $$\frac{25}{2}\bigl(B_2(r_{i,1}/25)+B_2(r_{i,2}/25)-B_2(r_{i+1,1}/25)-B_2(r_{i+1,2}/25)\bigr)=q_i.$$ This identifies the analytic Siegel exponent with the formal Laurent-series order.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false
open N25

theorem N25.unitResidues25_bernoulli_diff (i : Fin 5) :
    (25 / 2 : ℚ) *
      ((((unitResidues25 i).1 : ℚ) / 25) ^ 2 - ((unitResidues25 i).1 : ℚ) / 25 + 1 / 6 +
       (((unitResidues25 i).2 : ℚ) / 25) ^ 2 - ((unitResidues25 i).2 : ℚ) / 25 + 1 / 6 -
       ((((unitResidues25 (i + 1)).1 : ℚ) / 25) ^ 2 - ((unitResidues25 (i + 1)).1 : ℚ) / 25 + 1 / 6 +
        (((unitResidues25 (i + 1)).2 : ℚ) / 25) ^ 2 - ((unitResidues25 (i + 1)).2 : ℚ) / 25 + 1 / 6)) =
      (unitQOrder25 i : ℚ) := by sorry
