-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictTypeOne_or_isStrictTypeTwo
-- name    : ModularCurve.PlaceSpecialization.isStrictTypeOne_or_isStrictTypeTwo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/7ab906f2-872c-54e7-9b54-7b9879ac59b6
-- title:
--   Strict type dichotomy off the Frobenius-square-fixed locus
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} \colon A \to k$. Let `data` be modular polynomial data at $q$, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ vanishing on the $q$-th modular equation for the $j$-function, and let `hKr` be the Kronecker congruence for it, namely $\Phi \bmod q = (C(X)^q - X)(C(X) - X^q)$ after the bivariate reduction. Let `hα`, `hβ` assert that the two Hecke maps $\overline{\alpha}$, $\overline{\beta}$ at level $1$ and prime $q$ are integral ring homomorphisms, and let $P$ be a place specialisation `PlaceSpecialization A q 1 data hKr k red hα hβ`, whose component `sp` carries places of the level-one modular function field over $\overline{\mathbb Q}$ to places of `modularFunctionFieldC k 1`. Write $\varphi$ for `frobOnPlacesGeomLevel k 1 data hKr`, the self-map of the places of `modularFunctionFieldC k 1` obtained by restricting a place to the image of the geometric Frobenius and transporting it back along the Frobenius equivalence, and write $\mathrm{red}_1 W = P.\mathrm{sp}$ applied to the restriction of $W$ along $\overline{\alpha}$, with $\mathrm{red}_2 W$ the companion place attached to $P$. Then for every place $W$ of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$ with $\varphi^2(\mathrm{red}_1 W) \neq \mathrm{red}_1 W$, either $\varphi(\mathrm{red}_1 W) = \mathrm{red}_2 W$ together with $\varphi^2(\mathrm{red}_1 W) \neq \mathrm{red}_1 W$ (strict type one), or $\mathrm{red}_1 W = \varphi(\mathrm{red}_2 W)$ together with $\varphi^2(\mathrm{red}_2 W) \neq \mathrm{red}_2 W$ (strict type two).
--
--   This is the point-level component assignment for the reduction of $X_0(q)$ modulo $q$: by Kronecker's congruence the pair $(\mathrm{red}_1 W, \mathrm{red}_2 W)$ lies on the graph of the Frobenius or on its transpose, and away from the places fixed by $\varphi^2$ one of the two alternatives holds in the strict form recorded by the predicates `IsStrictTypeOne` and `IsStrictTypeTwo`. It is used to sort the support of divisors between the two components of the special fibre, in particular in the analysis of level-one prolongation pairs and of the multiplicative covering charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_isStrictTypeOne_or_isStrictTypeTwo.lean

import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularNodes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.isStrictTypeOne_or_isStrictTypeTwo
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hW : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redFst W))
      ≠ P.redFst W) :
    P.IsStrictTypeOne W ∨ P.IsStrictTypeTwo W := by sorry
