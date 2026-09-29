-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_le_sum_ramificationIndexAlong_heckeAlphaBar_filter_not_isInftySide_fiberAlong
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.le_sum_ramificationIndexAlong_heckeAlphaBar_filter_not_isInftySide_fiberAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/23a4f83d-38de-539a-90fd-d7bb0f0a3b9d
-- title:
--   Ramification mass off the ∞-side is at least q
-- statement:
--   Fix a prime $q$ and a valuation subring $A$ of an algebraic closure of $\mathbb{Q}$, an integer $N \neq 0$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Let `data` be a `ModularPolynomialData q`, that is a monic $\Phi \in \mathbb{Z}[X][Y]$ with $\deg \Phi = \psi(q)$ and $\Phi(j, j_q) = 0$, and let `hKr` be the Kronecker congruence for it, i.e. the reduction of $\Phi$ modulo $q$ equals $(C X^{q} - X)(C X - X^{q})$. Let `hα`, `hβ` assert that the two degeneracy inclusions $\alpha, \beta$ of the level-$N$ into the level-$Nq$ modular function field over $\overline{\mathbb{Q}}$, `heckeAlphaBar` and `heckeBetaBar`, are integral ring homomorphisms; the level-$Nq$ field is assumed to have principal divisors, in the sense that every nonzero function is the function of a degree-zero divisor. Assume $q \nmid N$, let $P$ be a `PlaceSpecialization` for these data (a structure packaging a map $sp$ from places of the level-$N$ field over $\overline{\mathbb{Q}}$ to places of the level-$N$ field over $k$, a homomorphism on degree-zero divisor classes, and compatibilities of orders of $j$, $j_N$ and related functions under reduction), and let $b$ be a place of the level-$N$ field over $\overline{\mathbb{Q}}$. Then $q$ is at most the sum, over those places $W$ in the fibre of $b$ along $\alpha$ (the finite set of places of the level-$Nq$ field whose restriction along $\alpha$ is $b$) for which `IsInftySide P W` fails, of the ramification index of $W$ over $b$ computed for the algebra structure given by $\alpha$. Here `IsInftySide P W` means that the predicate `IsCuspidal P W` holds and that there is $\tau \in A$ with $red(\tau) = 1$ at which $W$ takes the value $\tau$ on the chart function `tInfty N q`.
--
--   This is the general lower bound on the ramification carried by the places of $X_0(Nq)$ over a place of $X_0(N)$ that do not lie on the $\infty$-side; since the full fibre has ramification mass $q+1$, the degree of the first degeneracy map, it says equivalently that the $\infty$-side mass over any place is at most $1$. It is used to obtain the exact value $1$ for the $\infty$-side mass over places at which $j$ takes no value in $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_le_sum_ramificationIndexAlong_heckeAlphaBar_filter_not_isInftySide_fiberAlong.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option autoImplicit false
open AlgebraicCurve ModularCurve

open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.le_sum_ramificationIndexAlong_heckeAlphaBar_filter_not_isInftySide_fiberAlong
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (b : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    :
    (q : ℤ) ≤ ∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter
        (fun W => ¬ IsInftySide P W),
      (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ) := by sorry
