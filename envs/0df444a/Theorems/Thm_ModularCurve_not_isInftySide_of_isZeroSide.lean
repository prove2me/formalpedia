-- Prove2me | Theorems.Thm_ModularCurve_not_isInftySide_of_isZeroSide
-- name    : ModularCurve.not_isInftySide_of_isZeroSide
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/96e82ff5-d524-5cb0-af2e-bc20574e4192
-- title:
--   The 0-side and ∞-side of a cuspidal place are disjoint
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Let `data` be a `ModularPolynomialData` for $q$, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions, and let `hKr` be the Kronecker congruence for it: the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$. Let `hα` and `hβ` assert that the two degeneracy maps `heckeAlphaBar` and `heckeBetaBar` from the base-changed modular function field of level $1$ to that of level $1 \cdot q$ over $\overline{\mathbb Q}$ are integral. Let $P$ be a place specialisation of type `PlaceSpecialization A q 1 data hKr k red hα hβ`, and let $W$ be a place of the field `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$, i.e. a valuation subring, not the whole field, containing the image of $\overline{\mathbb Q}$ and a principal ideal ring. Assume $P$ and $W$ satisfy `IsZeroSide`: the predicate `IsCuspidal'` holds for $P$ and $W$, and there is $\tau \in A$ with $\mathrm{red}\,\tau = 1$ such that `tZero` lies in the valuation subring of $W$ and has residue the image of $\tau$. The conclusion is that `IsInftySide` fails for $P$ and $W$: it is not the case both that the predicate `IsCuspidal` holds for $P$ and $W$ and that there is $\tau \in A$ with $\mathrm{red}\,\tau = 1$ for which `tInfty` lies in the valuation subring of $W$ with residue the image of $\tau$.
--
--   This is the disjointness half of the cusp dichotomy for $X_0(q)$ in characteristic $q$, where the two branches of the fibre are described by the charts `tInfty` and `tZero`; together with the complementary statement that a cuspidal place lies on one of the two sides, it makes the cuspidal region a partition. It is used in the analysis of the multiplicative covering, where the two chart domains are shown to be disjoint and to partition the cusps, and in the Riemann–Roch estimate for residue pairs attached to level-one prolongation pairs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_not_isInftySide_of_isZeroSide.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.not_isInftySide_of_isZeroSide
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsZeroSide W) :
    ¬ P.IsInftySide W := by sorry
