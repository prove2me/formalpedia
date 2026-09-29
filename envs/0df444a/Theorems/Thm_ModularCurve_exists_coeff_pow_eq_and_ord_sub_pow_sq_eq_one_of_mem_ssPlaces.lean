-- Prove2me | Theorems.Thm_ModularCurve_exists_coeff_pow_eq_and_ord_sub_pow_sq_eq_one_of_mem_ssPlaces
-- name    : ModularCurve.exists_coeff_pow_eq_and_ord_sub_pow_sq_eq_one_of_mem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/ac424f2c-9f40-53af-bdd2-960e8b5d591f
-- title:
--   Order-one difference g-g^{q^2} at supersingular places
-- statement:
--   Fix a prime $q$ and a positive integer $N$ with $q \nmid N$, and an algebraically closed field $k$ of characteristic $q$ (with decidable equality). Work inside the field $F =$ `modularFunctionFieldC k N`, the intermediate field of the Laurent series field $k((q))$ generated over $k$ by the two series `jqModC k` and `jqNModC k N` (the $q$-expansions of $j$ and of $j$ after the substitution $q \mapsto q^N$). Let $w$ be a place of $F$ over $k$, i.e. a valuation subring of $F$ containing $k$, different from $F$, and a principal ideal ring, and assume $w$ lies in `ssPlaces q N k`: $w$ is rational, both generators `jGeomGen k N` and `jNGeomGen k N` lie in its valuation subring (i.e. $w$ is an affine geometric place), and the value of `jGeomGen k N` at $w$ belongs to `ssJSet q k`. The assertion is the existence of an element $\bar g \in F$ with three properties: every Laurent coefficient $c$ of $\bar g$ satisfies $c^q = c$; $\bar g$ lies in the valuation subring of every affine geometric place $u$ of $F$; and the element $\bar g - \bar g^{q^2}$ has order exactly $1$ both at $w$ and at the translate of $w$ by `arithFrobC q k N`, the semilinear automorphism of $F$ over $k$ obtained by applying the Frobenius $x \mapsto x^q$ to the coefficients of Laurent series, the order being $-\log$ of the associated adic valuation.
--
--   This supplies, at a supersingular point of the level-$N$ modular curve in characteristic $q$ and at its Frobenius translate, a globally regular function defined over $\mathbb{F}_q$ whose difference with its $q^2$-power power is a uniformiser; it is the shape in which the Riemann–Roch input is used by [`ModularCurve.PlaceSpecialization.exists_ord_sub_pow_sq_eq_one_of_mem_ssPlaces`](thm.html#ModularCurve.PlaceSpecialization.exists_ord_sub_pow_sq_eq_one_of_mem_ssPlaces).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_coeff_pow_eq_and_ord_sub_pow_sq_eq_one_of_mem_ssPlaces.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.exists_coeff_pow_eq_and_ord_sub_pow_sq_eq_one_of_mem_ssPlaces
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (hqN : ¬ q ∣ N) (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) :
    ∃ gbar : ↥(modularFunctionFieldC k N),
      (∀ n : ℤ, ((gbar : LaurentSeries k).coeff n) ^ q = (gbar : LaurentSeries k).coeff n) ∧
      (∀ u : Place k (modularFunctionFieldC k N), IsAffineGeomPlace k N u → gbar ∈ u.toValuationSubring) ∧
      w.ord (gbar - gbar ^ (q ^ 2)) = 1 ∧ (arithFrobC q k N • w).ord (gbar - gbar ^ (q ^ 2)) = 1 := by sorry
