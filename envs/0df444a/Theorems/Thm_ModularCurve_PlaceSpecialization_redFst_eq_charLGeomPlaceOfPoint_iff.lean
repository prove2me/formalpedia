-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff
-- name    : ModularCurve.PlaceSpecialization.redFst_eq_charLGeomPlaceOfPoint_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/9715f482-a379-5feb-9435-64a8f2870d1b
-- title:
--   Value-fibre criterion for the first reduction red₁
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Fix modular polynomial data `data` for $q$, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ vanishing on the pair of $q$-expansions attached to level $q$, subject to the Kronecker congruence `hKr`, which says that the bivariate reduction of $\Phi$ modulo $q$ equals $(C(X)^{q}-X)(C(X)-X^{q})$; fix also the hypotheses $h\alpha$, $h\beta$ that the two Hecke maps $\bar\alpha, \bar\beta$ from level $1$ to level $q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place specialization datum for these data at level $N = 1$, comprising a map $sp$ from places of $\overline{\mathbb Q}\,$-modular function field of level $1$ to places of the characteristic-$q$ modular function field $\mathrm{modularFunctionFieldC}\ k\ 1$, a homomorphism on degree-zero divisor class groups, and the compatibility conditions on the orders of $j$ and $j_N$ recorded in `PlaceSpecialization`. Let $W$ be a place of the level-$1\cdot q$ field $\mathrm{modularFunctionFieldBar}(1\cdot q)$ over $\overline{\mathbb Q}$ and let $c_0 \in k$. The assertion is that the first reduction $P.\mathrm{redFst}\,W$, namely $sp$ applied to the restriction of $W$ along the integral map $\bar\alpha$, equals the place $\mathrm{charLGeomPlaceOfPoint}\ k\ c_0$ of $\mathrm{modularFunctionFieldC}\ k\ 1$ — the place corresponding, under the identification of that field with the rational function field over $k$, to the finite place $X - c_0$ — if and only if there is $a \in A$ with $red\,a = c_0$ and $\mathrm{ord}_W\bigl(j - a\bigr) > 0$, where $j$ is the element `jFun` of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ given by the $q$-expansion of $j$ with coefficients in $\overline{\mathbb Q}$, $a$ is viewed in the field via the structure map, and $\mathrm{ord}$ is minus the logarithm of the adic valuation attached to the place.
--
--   This is the value-fibre description of the first reduction map: a place of the level-$q$ modular function field reduces to the point $c_0$ of the $j$-line in characteristic $q$ exactly when $j$ specializes at $W$ to a lift of $c_0$ in $A$. It is the tool that converts push-forwards along $\mathrm{redFst}$ into sums over value fibres of $j$, and is used in the analysis of the Deligne–Rapoport model package, in particular for identifying sections through crossing points and for order estimates on residues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_SpecializeModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.redFst_eq_charLGeomPlaceOfPoint_iff
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (c₀ : k) :
    P.redFst W = charLGeomPlaceOfPoint k c₀ ↔ ∃ a : A, red a = c₀ ∧
      0 < W.ord (PlaceSpecialization.jFun (q := q)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)) := by sorry
