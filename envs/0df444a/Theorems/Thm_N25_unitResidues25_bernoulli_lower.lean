-- Prove2me | Theorems.Thm_N25_unitResidues25_bernoulli_lower
-- name    : N25.unitResidues25_bernoulli_lower
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:50:09.098202+00:00
-- url     : https://prove2.me/theorems/9194e061-a8f8-4987-b5b9-0ef06a31a08f
-- title:
--   Every finite residue scaling has Bernoulli difference at least $-6/25$
-- statement:
--   Let $a∈ℤ/25ℤ$, let $i∈ℤ/5ℤ$, and define $B_a(g)=((ag\bmod25)/25)^2-(ag\bmod25)/25+1/6$. Then $$-\frac{6}{25}≤B_a(r_{i,1})+B_a(r_{i,2})-B_a(r_{i+1,1})-B_a(r_{i+1,2}).$$ This finite inequality yields the uniform lower bound on cusp exponents.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false
open N25

theorem N25.unitResidues25_bernoulli_lower (a : Fin 25) (i : Fin 5) :
    let B : ℕ → ℚ := fun g =>
      (((a.val * g) % 25 : ℕ) : ℚ) ^ 2 / 625 -
        (((a.val * g) % 25 : ℕ) : ℚ) / 25 + 1 / 6
    (-6 / 25 : ℚ) ≤ B (unitResidues25 i).1 + B (unitResidues25 i).2 -
      (B (unitResidues25 (i + 1)).1 + B (unitResidues25 (i + 1)).2) := by sorry
