-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/31afaa11-a5fc-54d7-bd82-3d7811b87bf3
-- title:
--   The ∞-side cusps over a cusp have ramification sum one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ (an algebraic closure of $\mathbb{Q}$), a positive integer $N$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$, together with data $data$ consisting of a monic polynomial $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the $q$-expansion datum at level $q$, a witness $hKr$ that the reduction of $\Phi$ modulo $q$ equals $(\mathrm{C}\,X^{q} - X)(\mathrm{C}\,X - X^{q})$, and witnesses $h\alpha$, $h\beta$ that the two degeneracy inclusions `heckeAlphaBar`, `heckeBetaBar` of the base-changed level-$N$ modular function field over $\overline{\mathbb{Q}}$ into the level-$Nq$ one are integral ring maps; the level-$Nq$ field is assumed to have principal divisors, i.e. every nonzero element is the divisor of degree $0$ given by its orders at all places. Assume $q \nmid N$, let $P$ be a place specialization in the sense of `PlaceSpecialization` (a map $sp$ from places of the level-$N$ field over $\overline{\mathbb{Q}}$ to places of the level-$N$ field over $k$, a homomorphism on cuspidal divisor classes, and compatibility conditions relating orders of $j$, $j_N$ and related functions to their reductions), and let $b$ be a place of the base-changed level-$N$ modular function field over $\overline{\mathbb{Q}}$ at which the coefficientwise image of the $q$-expansion of $j$ has strictly negative order, i.e. a pole of $j$. Then the sum, over those places $W$ of the level-$Nq$ field lying in the fibre of $b$ along `heckeAlphaBar` which satisfy `IsInftySide P` (namely $W$ is cuspidal for $P$ and the chart function `tInfty N q` takes at $W$ a value $\tau \in A$ with $red\,\tau = 1$), of the ramification indices $e(W)$ of $W$ along `heckeAlphaBar`, regarded as integers, equals $1$.
--
--   Classically this is the statement that over a cusp of $X_0(N)$ the first degeneracy map $X_0(Nq) \to X_0(N)$ has exactly one cusp on the $\infty$-side, and that this cusp is unramified, the other cusp in the fibre carrying the whole ramification index $q$. It is used in the computations of divisors of modular units on the $\infty$-side and in identifying the pushforward of such divisors under the specialization map $sp$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve ModularCurve
open Classical in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.sum_ramificationIndexAlong_heckeAlphaBar_filter_isInftySide_fiberAlong_eq_one
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
    (hb : b.ord ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full N (jq_mem N))⟩ < 0) :
    (∑ W ∈ (Place.fiberAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα b).filter (IsInftySide P),
        (W.ramificationIndexAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) : ℤ)) = 1 := by sorry
