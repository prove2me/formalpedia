-- Prove2me | Theorems.Thm_ModularCurve_ncard_setOf_ord_jGeomGen_eq_three_and_eq_six_of_exists_prime_dvd_mod_three_eq_two
-- name    : ModularCurve.ncard_setOf_ord_jGeomGen_eq_three_and_eq_six_of_exists_prime_dvd_mod_three_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/ab3c0021-f748-588b-b605-bb4b812e7aa3
-- title:
--   Places of j-order exactly 3 and 6 in characteristic 3
-- statement:
--   Let $N'$ be a nonzero natural number with $3 \nmid N'$ which is divisible by at least one prime $q$ with $q \equiv 2 \pmod 3$, and let $F$ be an algebraically closed field of characteristic $3$. Consider the intermediate field [`ModularCurve.modularFunctionFieldC F N'`](def/ModularCurve_JqCoeff.html#L61) of the field of Laurent series over $F$, namely the subfield generated over $F$ by the two series $q^{-1}\cdot\,$(the reduction of the $j$-numerator) and its $N'$-th $q$-expansion, and let [`ModularCurve.jGeomGen F N'`](def/ModularCurve_CharLSpecialFibreLevelNDictionary.html#L82) denote the first of these two generators as an element of that field. For a place $w$ of this field over $F$ — a valuation subring containing $F$, distinct from the whole field, whose underlying ring is a principal ideal ring — let $w.\mathrm{ord}$ be the integer-valued order function attached to its associated height-one valuation. Then, as an identity of rational numbers, the number of places $w$ with $w.\mathrm{ord}(\mathrm{jGeomGen}\ F\ N') = 3$ equals the number of $x \in \mathbb{Z}/N'$ with $x^2 + 1 = 0$, and the number of places with order exactly $6$ equals $\psi(N')/6 - \nu_2(N')/2$, where $\psi(N') = \sum_{d \mid N',\ d \text{ squarefree}} N'/d$ and $\nu_2(N')$ is the count above.
--
--   In characteristic $3$ the unique supersingular $j$-invariant is $0$, so these are the places of the level-$N'$ modular function field lying over the supersingular point, sorted by the order of vanishing of $j$; the divisibility hypothesis on $N'$ rules out the orders $1$ and $2$, and the total order of vanishing is $\psi(N')$. The result feeds the computation of degrees in terms of weight floors in characteristic $3$, via [`ModularCurve.degree_eq_of_forall_eq_weightFloor_of_charP_three`](thm.html#ModularCurve.degree_eq_of_forall_eq_weightFloor_of_charP_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ncard_setOf_ord_jGeomGen_eq_three_and_eq_six_of_exists_prime_dvd_mod_three_eq_two.lean

import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.ncard_setOf_ord_jGeomGen_eq_three_and_eq_six_of_exists_prime_dvd_mod_three_eq_two
    (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (F : Type) [Field F] [CharP F 3] [IsAlgClosed F] :
    (Set.ncard {w : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N') |
        w.ord (ModularCurve.jGeomGen F N') = 3} : ℚ) = (ModularCurve.nuTwo N' : ℚ) ∧
      (Set.ncard {w : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N') |
        w.ord (ModularCurve.jGeomGen F N') = 6} : ℚ) =
        (ModularCurve.dedekindPsi N' : ℚ) / 6 - (ModularCurve.nuTwo N' : ℚ) / 2 := by sorry
