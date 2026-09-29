-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictTypeOne_frickeInvolutionBar_smul_iff
-- name    : ModularCurve.PlaceSpecialization.isStrictTypeOne_frickeInvolutionBar_smul_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/bd1fcb63-bc41-5d9b-acc9-6d24415bea43
-- title:
--   Fricke involution exchanges strict types one and two
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Let `data` consist of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ with $\Phi(j, j_q) = 0$, and let $hKr$ be the Kronecker congruence $\Phi \bmod q = (X^q - Y)(X - Y^q)$ for this $\Phi$. Let $h\alpha$, $h\beta$ assert that the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` of the geometric modular function field of level $1$ into that of level $1 \cdot q$ over $\overline{\mathbb Q}$ are integral, and let $P$ be a place specialisation for these data, so in particular $P$ carries a map $P.\mathrm{sp}$ from places of $\overline{\mathbb Q}$-modular function fields to places over $k$, compatible with the $j$-functions. Let $W$ be a place of `modularFunctionFieldBar (1 * q)`, i.e. a proper valuation subring containing $\overline{\mathbb Q}$ whose ring is a principal ideal ring, and write $\mathrm{red}_1 W$, $\mathrm{red}_2 W$ for the places over $k$ obtained by restricting $W$ along `heckeAlphaBar`, respectively `heckeBetaBar`, and applying $P.\mathrm{sp}$. Writing $\varphi$ for `frobOnPlacesGeomLevel`, the assertion is: the translate of $W$ by the Fricke involution `frickeInvolutionBar (1 * q)` satisfies $\varphi(\mathrm{red}_1) = \mathrm{red}_2$ together with $\varphi^2(\mathrm{red}_1) \neq \mathrm{red}_1$ if and only if $W$ itself satisfies $\mathrm{red}_1 W = \varphi(\mathrm{red}_2 W)$ together with $\varphi^2(\mathrm{red}_2 W) \neq \mathrm{red}_2 W$.
--
--   This is the place-level form of the classical fact that the Atkin–Lehner (Fricke) involution $w_q$ interchanges the two components of the special fibre of $X_0(q)$ at $q$: it swaps the two strict types distinguished by the Kronecker congruence. It is used in the analysis of the multiplicative covering, for the statements about membership of the cuspidal charts at $\infty$ and at $0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_isStrictTypeOne_frickeInvolutionBar_smul_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.isStrictTypeOne_frickeInvolutionBar_smul_iff
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.IsStrictTypeOne (frickeInvolutionBar (1 * q) • W) ↔ P.IsStrictTypeTwo W := by sorry
