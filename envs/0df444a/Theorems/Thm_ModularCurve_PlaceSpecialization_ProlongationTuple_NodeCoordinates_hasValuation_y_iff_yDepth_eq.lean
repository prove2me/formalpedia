-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_hasValuation_y_iff_yDepth_eq
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.hasValuation_y_iff_yDepth_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/1fff07c3-86a4-5c0f-b0ba-d973fff6ddf4
-- title:
--   Relational depth equals value-group depth of y
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a nonzero level $N$, a field $k$ of characteristic $q$ which is perfect, and a ring homomorphism $red : A \to k$; fix modular polynomial data for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$), a proof $hKr$ that its bivariate reduction mod $q$ factors as $(X^q - Y)(X - Y^q)$ in the Kronecker form, and proofs $h\alpha$, $h\beta$ that the two Hecke correspondence maps $\overline{\mathbb Q}$-rationally are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` for these data, $R$ a `ProlongationTuple` over $P$, $K$ an intermediate field of $\overline{\mathbb Q}/\mathbb Q$, $w$ a place of the level-$N$ function field $\mathrm{modularFunctionFieldC}\,k\,N$, and $c$ a tuple of node coordinates for $R$, $K$, $w$: elements $x,y$ of the subring $R.\mathrm{nodeIntegersOver}\,K\,w$ with $x$ killed by the first residue map, $y$ killed by the second, $\mathrm{ord}_w$ of the first residue of $y$ equal to $1$, and $\mathrm{ord}$ of the second residue of $x$ equal to $1$ at the Frobenius translate of $w$. Let $V$ be a place of $\overline{\mathbb Q}$ on the level-$Nq$ field $\mathrm{modularFunctionFieldBar}(Nq)$ whose first reduction $P.\mathrm{reduceFst}\,V$ is $w$, assume $V$ is rational, i.e. $\overline{\mathbb Q}$ surjects onto the residue field of $V$, and let $\gamma$ lie in the value group of $A$. Then there exists $a \in \overline{\mathbb Q}$ with $y(V) = a$ in the sense of the value relation of $V$ and $v_A(a) = \gamma$ if and only if $v_A$ of the evaluation of $y$ at $V$ equals $\gamma$, the latter being by definition $c.\mathrm{yDepth}\,V = \gamma$.
--
--   This is the compatibility of the two ways of measuring the depth of the node parameter $y$ at a place above the node: the existential, relation-based formulation through `HasValuation`, and the value-group-valued function `yDepth` obtained from evaluation at the place. It is used by the depth estimates at nodes of the level-$Nq$ curve, such as the bounds `depth_lt_mul_of_yDepth_pow_eq` and the results deducing strict positivity and upper bounds for depths from the node equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_NodeCoordinates_hasValuation_y_iff_yDepth_eq.lean

import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_AlgebraicCurve_PlaceDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.NodeCoordinates.hasValuation_y_iff_yDepth_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) [PerfectField k] {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
    {w : Place k (modularFunctionFieldC k N)} (c : R.NodeCoordinates K w)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hVw : P.reduceFst V = w) (hV : V.IsRational)
    (γ : A.ValueGroup) :
    V.HasValuation A ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) γ ↔ c.yDepth V = γ := by sorry
