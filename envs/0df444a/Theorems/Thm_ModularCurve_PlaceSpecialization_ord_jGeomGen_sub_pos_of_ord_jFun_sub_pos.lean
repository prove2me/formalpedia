-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos
-- name    : ModularCurve.PlaceSpecialization.ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/d455c084-1c08-5d92-a5b3-ea8043598dd4
-- title:
--   Zeros of j-j₀ descend along the first reduction
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an integer $N\ge 1$, and an algebraically closed field $k$ of characteristic $q$ (with decidable equality) together with a ring homomorphism $\mathrm{red}\colon A\to k$. Fix further data $\mathrm{data}$ of type `ModularPolynomialData q`, i.e. a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$ of $q$-expansions, a proof `hKr` that $\Phi$ reduces modulo $q$ to $(X^q-Y)(X-Y^q)$ in the bivariate normalisation used, and proofs `hα`, `hβ` that the two Hecke maps $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ for level $N$ and prime $q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place specialisation for these data: among its components are a map $\mathrm{sp}$ from places of $\overline{\mathbb Q}(X_0(N))=\mathrm{modularFunctionFieldBar}\,N$ to places of $\mathrm{modularFunctionFieldC}\,k\,N=k(j_{\mathrm{mod}},j_{N,\mathrm{mod}})\subseteq k((q))$, a homomorphism on degree-zero divisor classes, and compatibility axioms, of which the relevant one states that $\mathrm{ord}_w(j-a)>0$ implies $\mathrm{ord}_{\mathrm{sp}(w)}(j_{\mathrm{mod}}-\mathrm{red}\,a)>0$ for every place $w$ and every $a\in A$. Let $Q$ be a place of $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb Q}$, that is, a proper valuation subring containing $\overline{\mathbb Q}$ whose ring is a principal ideal ring, and let $j_0\in A$. Assume $\mathrm{ord}_Q\bigl(\mathrm{jFun}\,N\,q-j_0\bigr)>0$, where $\mathrm{jFun}\,N\,q$ is the coefficientwise image of the $q$-expansion of $j$ inside $\mathrm{modularFunctionFieldBar}(Nq)$ and $\mathrm{ord}$ is minus the logarithm of the associated adic valuation. Then $\mathrm{ord}$ of $\mathrm{jGeomGen}\,k\,N-\mathrm{red}\,j_0$ at $P.\mathrm{reduceFst}\,Q=\mathrm{sp}$ applied to the restriction of $Q$ along $\mathrm{heckeAlphaBar}$ is strictly positive.
--
--   This is the level-$N$ form of the surviving implication in the dictionary between places of $X_0(Nq)$ over $\overline{\mathbb Q}$ and places of the characteristic-$q$ special fibre: a place at which $j$ takes the value $j_0\in A$ reduces, under the first of the two reduction maps attached to the Hecke correspondence, to a place at which the geometric $j$-invariant takes the value $\mathrm{red}\,j_0$. At level $N$ a place of $k(X_0(N))$ is not determined by its $j$-value, so only this implication is asserted; it is used in the identification of crossing points and of ord-values of reduced $j$-differences on models of $X_0(Nq)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos.lean

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (Q : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (j₀ : A)
    (hQ : 0 < Q.ord (ProlongationTuple.jFun N q - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (j₀ : AlgebraicClosure ℚ))) :
    0 < (P.reduceFst Q).ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (red j₀)) := by sorry
