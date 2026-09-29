-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar
-- name    : ModularCurve.PlaceSpecialization.redFst_cuspInftyBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/b532e48e-ef00-5e8e-90b8-82b8ef072483
-- title:
--   First reduction of the cusp ∞̄ is the j-line cusp
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a field $k$ of characteristic $q$, and a ring homomorphism $\mathrm{red} : A \to k$. Fix further modular polynomial data `data` for level $q$, i.e. a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions, together with the Kronecker congruence hypothesis `hKr` asserting that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)\,(C(X) - X^q)$, and the hypotheses `hα`, `hβ` that the two degeneracy inclusions $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ from the base-changed level-$1$ Laurent modular function field to the level-$q$ one are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` datum for these parameters at level $N = 1$: a map $\mathrm{sp}$ from places of $\mathrm{modularFunctionFieldBar}\,1$ over $\overline{\mathbb{Q}}$ to places of the characteristic-$q$ model $\mathrm{modularFunctionFieldC}\,k\,1$, a homomorphism on degree-zero divisor classes, and the compatibility axioms relating orders of $j - a$ and $j_N - a$ to the orders of their reductions along $\mathrm{red}$. The conclusion is that $P.\mathrm{redFst}$ — restriction of a place of $\mathrm{modularFunctionFieldBar}\,(1\cdot q)$ along $\mathrm{heckeAlphaBar}$ followed by $\mathrm{sp}$ — sends the place $\mathrm{cuspInftyBar}\,(1\cdot q)$, the place given by $q$-expansions at infinity, to the image under $\mathrm{charLGeomPlaceEquiv}\,k$ of the place $\mathrm{placeInfty}\,k$, the valuation subring of the infinity valuation of $k(T)$.
--
--   This identifies the first level-one reduction of the cusp at infinity of $X_0(q)_{\overline{\mathbb{Q}}}$ with the cusp $\tilde\jmath = \infty$ of the $j$-line over $k$. It is the anchor that lets statements formulated at $\mathrm{redFst}$ of the cusp be read at the named infinity place of the rational function field, and it is used throughout the analysis of the multiplicative covering and of charts near the cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ModularCurve_AtkinLehner

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.redFst_cuspInftyBar
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq (RatFunc k)] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    P.redFst (cuspInftyBar (1 * q)) = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k) := by sorry
