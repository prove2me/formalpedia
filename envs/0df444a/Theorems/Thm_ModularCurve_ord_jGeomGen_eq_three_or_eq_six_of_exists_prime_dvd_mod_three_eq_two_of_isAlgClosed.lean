-- Prove2me | Theorems.Thm_ModularCurve_ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
-- name    : ModularCurve.ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/201c39a1-d53a-563f-bb6f-b7281e9c47a8
-- title:
--   Order of vanishing of ̄ j at supersingular places in characteristic 3
-- statement:
--   Let $N'$ be a nonzero natural number with $3 \nmid N'$, and suppose some prime $q$ divides $N'$ with $q \equiv 2 \pmod 3$. Let $F$ be an algebraically closed field of characteristic $3$, and let $M =$ [`ModularCurve.modularFunctionFieldC F N'`](def/ModularCurve_JqCoeff.html#L61) be the intermediate field of the field $F((q))$ of Laurent series generated over $F$ by the two elements `jqModC F` (the reduction to $F$ of the $q$-expansion of the modular invariant, namely $q^{-1}$ times the power series with coefficients the images of the integral coefficients of $j$) and `jqNModC F N'` (its image under the substitution $q \mapsto q^{N'}$). Let $x$ be a place of $M$ over $F$, i.e. a valuation subring of $M$ containing the image of $F$, distinct from $M$ itself, and a principal ideal ring; write $x.\mathrm{ord}$ for the associated normalised integer valuation, the negative of the logarithm of the height-one adic valuation. Let $j =$ [`ModularCurve.jGeomGen F N'`](def/ModularCurve_CharLSpecialFibreLevelNDictionary.html#L82) be the element `jqModC F` of $M$. If $x.\mathrm{ord}(j) > 0$, then $x.\mathrm{ord}(j) = 3$ or $x.\mathrm{ord}(j) = 6$.
--
--   In characteristic $3$ the unique supersingular value of the modular invariant is $j = 0$, so the places occurring here are the supersingular places of the modular curve of level $N'$, and the assertion computes the ramification index of such a place over the zero of $j$ on the $j$-line: it equals the index of the stabiliser of the level structure in the automorphism group modulo $\pm 1$ of the supersingular curve, which has order $6$, the hypothesis that a prime $q \equiv 2 \pmod 3$ divides $N'$ excluding stabilising automorphisms of order $3$. It is used in the study of mod $3$ modular forms, in particular for the statements about the ladder operator and the nonvanishing of restrictions in `ModPForms`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed.lean

import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.ord_jGeomGen_eq_three_or_eq_six_of_exists_prime_dvd_mod_three_eq_two_of_isAlgClosed
    (N' : ℕ) [NeZero N'] (hpN' : ¬ 3 ∣ N') (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N' ∧ q % 3 = 2)
    (F : Type) [Field F] [CharP F 3] [IsAlgClosed F]
    (x : AlgebraicCurve.Place F ↥(ModularCurve.modularFunctionFieldC F N'))
    (hx : 0 < x.ord (ModularCurve.jGeomGen F N')) :
    x.ord (ModularCurve.jGeomGen F N') = 3 ∨ x.ord (ModularCurve.jGeomGen F N') = 6 := by sorry
