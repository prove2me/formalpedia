-- Prove2me | Theorems.Thm_N25_unitResidues25_bernoulli_zero_of_five_dvd
-- name    : N25.unitResidues25_bernoulli_zero_of_five_dvd
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:40.328052+00:00
-- url     : https://prove2.me/theorems/edbc3411-b93e-41e6-b48e-4e593b318b3e
-- title:
--   Multiples of five give zero Bernoulli difference
-- statement:
--   Let $a∈ℤ$ be divisible by $5$, let $i∈ℤ/5ℤ$, and define $B_a(g)=((ag\bmod25)/25)^2-(ag\bmod25)/25+1/6$. Then $$B_a(r_{i,1})+B_a(r_{i,2})-B_a(r_{i+1,1})-B_a(r_{i+1,2})=0.$$ This explains the finite nonzero limits at cusps whose lower-left entry is divisible by $5$ but not by $25$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitSeries

set_option autoImplicit false
open N25

theorem N25.unitResidues25_bernoulli_zero_of_five_dvd (a : ℤ) (ha : 5 ∣ a) (i : Fin 5) :
    let B : ℕ → ℚ := fun g =>
      (((a * (g : ℤ)) % 25 : ℤ) : ℚ) ^ 2 / 625 -
        (((a * (g : ℤ)) % 25 : ℤ) : ℚ) / 25 + 1 / 6
    B (unitResidues25 i).1 + B (unitResidues25 i).2 -
      (B (unitResidues25 (i + 1)).1 + B (unitResidues25 (i + 1)).2) = 0 := by sorry
