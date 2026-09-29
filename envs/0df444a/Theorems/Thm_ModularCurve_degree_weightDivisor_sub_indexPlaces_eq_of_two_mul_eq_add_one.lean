-- Prove2me | Theorems.Thm_ModularCurve_degree_weightDivisor_sub_indexPlaces_eq_of_two_mul_eq_add_one
-- name    : ModularCurve.degree_weightDivisor_sub_indexPlaces_eq_of_two_mul_eq_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/2862e50a-59b5-570d-8061-50d7fca31f55
-- title:
--   Degree of the edge weight divisor at 2m = p+1
-- statement:
--   Let $p \ge 5$ be a prime and let $K$ be an algebraically closed field of characteristic $p$, and let $N$ be a nonzero natural number such that the function field $F =$ `modularFunctionFieldC K N`, the intermediate field of the Laurent series field $K((q))$ generated over $K$ by `jqModC K` and `jqNModC K N`, is a curve over $K$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15): every nonzero element of $F$ has a principal divisor of degree $0$, each place has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank $1$ over $F$. Assume $(N : K) \ne 0$, and let $m \ge 1$ satisfy $2m = p+1$. Let $SS$ be a finite set of places of $F$ over $K$ whose members are exactly the elements of `ssPlaces p N K`, the set of places $w$ with `IsSupersingularPlace p N K w`. Let $D'$ be a divisor of $F/K$, i.e. a finitely supported integer-valued function on places, such that $D' w =$ `weightDivisor K N m w` $- 1$ at every $w \in$ `ssPlaces p N K` with `placeWidth N w` dividing $m$ in $\mathbb{Z}$, and $D' w =$ `weightDivisor K N m w` at every $w$ for which it is not the case that both $w$ is in `ssPlaces p N K` and `placeWidth N w` divides $m$; here `weightDivisor K N m` is the divisor whose value at each place is `weightFloor K N m w`, when such a divisor exists, and $0$ otherwise. The conclusion is that the degree of $D'$, the sum of $D' w$ weighted by the residue degree of $w$, equals, as a rational number, $2\,g - 2 + \nu_\infty$, where $g =$ `genusFormula N` $= 1 + \psi(N)/12 - \nu_2(N)/4 - \nu_3(N)/3 - \nu_\infty/2$, $\nu_2(N)$ and $\nu_3(N)$ are the numbers of solutions of $x^2+1=0$ and $x^2+x+1=0$ in $\mathbb{Z}/N$, and $\nu_\infty =$ `cuspCount N` $= \sum_{d \mid N} \varphi(\gcd(d, N/d))$.
--
--   This is the numerical heart of the extremal case $2m = p+1$ of the weight bound on the modular curve of level $N$ in characteristic $p$: at this weight every supersingular place has width dividing $m$, so subtracting one at each supersingular place brings the degree of the weight-$m$ floor divisor down exactly to the canonical value $2g-2$ plus the number of cusps. It combines the degree formula for floor divisors, the Deuring–Eichler count of supersingular points with its elliptic corrections, and the genus and cusp formulae, and it is used in [`ModularCurve.omegaSpace_eq_bot_of_two_mul_eq_add_one`](thm.html#ModularCurve.omegaSpace_eq_bot_of_two_mul_eq_add_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_degree_weightDivisor_sub_indexPlaces_eq_of_two_mul_eq_add_one.lean

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.degree_weightDivisor_sub_indexPlaces_eq_of_two_mul_eq_add_one
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    [AlgebraicCurve.IsCurveOver K ↥(modularFunctionFieldC K N)]
    (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m) (hedge : 2 * m = p + 1)
    (SS : Finset (AlgebraicCurve.Place K ↥(modularFunctionFieldC K N))) (hSS : ∀ x, x ∈ SS ↔ x ∈ ssPlaces p N K)
    (D' : AlgebraicCurve.Divisor K ↥(modularFunctionFieldC K N))
    (hD'1 : ∀ w, w ∈ ssPlaces p N K → ((placeWidth N w : ℤ) ∣ (m : ℤ)) → D' w = ModularCurve.weightDivisor K N m w - 1)
    (hD'0 : ∀ w, ¬ (w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) → D' w = ModularCurve.weightDivisor K N m w) :
    (AlgebraicCurve.Divisor.degree D' : ℚ) = 2 * genusFormula N - 2 + (cuspCount N : ℚ) := by sorry
