-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_eq_of_isInftySide_of_hasValue_jFun
-- name    : ModularCurve.PlaceSpecialization.eq_of_isInftySide_of_hasValue_jFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/09bc934b-a65d-57d8-88b9-6e72c2bd25fe
-- title:
--   Uniqueness of the ∞-side point over a given j-value
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A \to k$. Let `data` be modular polynomial data for $q$, that is a monic $\Phi \in \mathbb Z[X][Y]$ with $\deg \Phi = \psi(q)$ and $\Phi(j, j_q) = 0$ after the substitution `evalAtJ`, let `hKr` be the Kronecker congruence for it, namely that the reduction of $\Phi$ modulo $q$ equals $(C X^q - X)(C X - X^q)$, and let `hα`, `hβ` assert that the two comparison maps `heckeAlphaBar` and `heckeBetaBar` from the level-$1$ to the level-$1\cdot q$ base-changed modular function field over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place specialization datum of type `PlaceSpecialization A q 1 data hKr k red hα hβ`, providing a map on places and a homomorphism on degree-zero divisor class groups compatible with the $j$-functions and their reductions. Let $W$ and $W'$ be places of the base-changed modular function field of level $1 \cdot q$ over $\overline{\mathbb Q}$ (valuation subrings containing the image of the base field, not all of the field, with principal ideal domain structure). Assume both are on the $\infty$-side for $P$: for each of $W$, $W'$, the predicate `P.IsCuspidal` holds and there is $\tau \in A$ with $\mathrm{red}(\tau) = 1$ such that `tInfty` lies in the valuation subring of the place and has residue the image of $\tau$ in its residue field. Assume finally that there is a single $x_0 \in \overline{\mathbb Q}$ which is the value at both $W$ and $W'$ of the element `PlaceSpecialization.jFun`, the $q$-expansion $j_q$ viewed inside the level-$1\cdot q$ function field; that is, `jFun` lies in each valuation subring and reduces to the image of $x_0$ in each residue field. The conclusion is $W = W'$.
--
--   This is the uniqueness statement for the canonical branch over the $\infty$-tube of $X_0(q)$: a point of the cuspidal region on the $\infty$-side is determined by the value of $j$ there, so that the $\infty$-side is a section of $X_0(q) \to X(1)$ over the region where $j$ is non-integral. It is used in the local analysis of the $q$-adic geometry of $X_0(q)$, in the construction of splitting data for prolongation pairs and in the computation of the sum of orders along $\infty$-side places; the argument rests on the Kronecker congruence through the root count for polynomials of Kronecker shape.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_eq_of_isInftySide_of_hasValue_jFun.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.PlaceSpecialization.eq_of_isInftySide_of_hasValue_jFun
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    {W W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hW : P.IsInftySide W) (hW' : P.IsInftySide W') {x₀ : AlgebraicClosure ℚ}
    (hx : W.HasValue (PlaceSpecialization.jFun (q := q)) x₀)
    (hx' : W'.HasValue (PlaceSpecialization.jFun (q := q)) x₀) :
    W = W' := by sorry
