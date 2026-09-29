-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_redSnd_cuspZeroBar
-- name    : ModularCurve.PlaceSpecialization.redSnd_cuspZeroBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/48b916cb-610b-572d-bd81-3ab532971271
-- title:
--   Second reduction of the cusp ̄ 0 at q
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $k$ be a field of characteristic $q$ and let $\mathrm{red} : A \to k$ be a ring homomorphism. Let `data` be a modular polynomial datum for $q$, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_{q\cdot})$ under the specified evaluation, let `hKr` be the hypothesis that the bivariate reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, and let `hα`, `hβ` be the hypotheses that the two degeneracy maps `heckeAlphaBar` and `heckeBetaBar` from level $1$ to level $q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` for these data: a map `sp` sending places of the level-one function field $\overline{\mathbb Q}$-curve to places of `modularFunctionFieldC k 1`, together with a homomorphism on degree-zero divisor class groups and the compatibility conditions on orders of $j$ and of the level functions under $\mathrm{red}$ (summarised here). The assertion is that $P.\mathrm{redSnd}$, namely the specialisation under `sp` of the restriction along `heckeBetaBar`, sends the cusp $\overline 0$ of level $1 \cdot q$ — defined as the image of the cusp $\overline\infty$ (the $q$-expansion place attached to $j$) under the Fricke involution — to the place of `modularFunctionFieldC k 1` obtained by transporting, along the isomorphism with $\mathrm{RatFunc}\,k$, the place `placeInfty k` given by the valuation subring of the infinite valuation on $k(T)$.
--
--   This records that the cusp $\overline 0$ of $X_0(q)$ reduces, on the second component of the special fibre at $q$, to the point at infinity of the $j$-line, the companion of the corresponding statement for $\overline\infty$ on the first component. It is used when cusp laws of a level-one prolongation pair are evaluated at the reduction of $\overline 0$ while the available bounds are stated at the cusp of the $j$-line.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_redSnd_cuspZeroBar.lean

import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.redSnd_cuspZeroBar
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq (RatFunc k)] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    P.redSnd (cuspZeroBar (1 * q)) = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k) := by sorry
