-- Prove2me | Theorems.Thm_N25_unitResidues25_bernoulli_lower_int
-- name    : N25.unitResidues25_bernoulli_lower_int
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:59.201507+00:00
-- url     : https://prove2.me/theorems/f64b96b6-31c2-4464-a011-94bb2a6121b4
-- title:
--   The Bernoulli lower bound holds for every integer scaling
-- statement:
--   Let $a∈ℤ$, let $i∈ℤ/5ℤ$, and define $B_a(g)=((ag\bmod25)/25)^2-(ag\bmod25)/25+1/6$ using the integer remainder modulo $25$. Then $$-\frac{6}{25}≤B_a(r_{i,1})+B_a(r_{i,2})-B_a(r_{i+1,1})-B_a(r_{i+1,2}).$$ This is the integer form used in transformed cusp expansions.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false
open N25

theorem N25.unitResidues25_bernoulli_lower_int (a : ℤ) (i : Fin 5) :
    let B : ℕ → ℚ := fun g =>
      (((a * (g : ℤ)) % 25 : ℤ) : ℚ) ^ 2 / 625 -
        (((a * (g : ℤ)) % 25 : ℤ) : ℚ) / 25 + 1 / 6
    (-6 / 25 : ℚ) ≤ B (unitResidues25 i).1 + B (unitResidues25 i).2 -
      (B (unitResidues25 (i + 1)).1 + B (unitResidues25 (i + 1)).2) := by sorry
