-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_hasValue_of_isInftySide
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_hasValue_of_isInftySide
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/f17ce375-f018-5535-973e-546f33e8baca
-- title:
--   Integral values of functions on the ∞-side
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$. Fix modular polynomial data `data` for $q$ (a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ killing the pair $(j,j_q)$) satisfying the Kronecker congruence $\overline\Phi=(X^q-Y)(X-Y^q)$, integrality hypotheses $h\alpha,h\beta$ for the two Hecke maps at level $1$ and prime $q$, a place specialisation $P$ of the places and degree-zero divisor classes of $\mathrm{modularFunctionFieldBar}(1)$ over these data, and a level-one prolongation pair $R$ for $P$, whose first member is a regular prolongation $R.R_1$ of $A$ to $\mathrm{modularFunctionFieldBar}(1\cdot q)$ with residue map into $\mathrm{modularFunctionFieldFullC}(\mathrm{ResidueField}\,A)\,1$, and whose associated reduction $R.\mathrm{residue}_1$ takes values in $\mathrm{modularFunctionFieldC}\,k\,1$. Let $W$ be a place of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ over $\overline{\mathbb Q}$ lying on the $\infty$-side for $P$, i.e. $W$ is $P$-cuspidal and there is $\tau\in A$ with $\mathrm{red}\,\tau=1$ and $t_\infty$ taking the value $\tau$ at $W$. Let $r$ be an element of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ lying in the valuation subring $R.R_1.\mathrm{integers}$ and in the valuation subring of every $\infty$-side place. Then there is $c\in A$ such that $r$ lies in the valuation subring of $W$ with residue the image of $c$, and the reduction $R.\mathrm{residue}_1(r)$ lies in the valuation subring of the place $P.\mathrm{redFst}\,W$ (the image under $P.\mathrm{sp}$ of the restriction of $W$ along $\mathrm{heckeAlphaBar}$) with residue the image of $\mathrm{red}\,c$.
--
--   This is the non-archimedean maximum principle on the residue disc of the cusp $\overline\infty$ of the first component in characteristic $q$: a function integral at the whole $\infty$-side takes a value in $A$ at each such place, and reduction of the value agrees with the value of the reduction. It is used in the construction of the first-component chart data, via [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFstSupply_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFstSupply_of_isModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_hasValue_of_isInftySide.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_hasValue_of_isInftySide
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair)
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (hW : P.IsInftySide W)
    (r : ↥(modularFunctionFieldBar (1 * q))) (h₁ : r ∈ R.R₁.integers)
    (hr : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsInftySide W' → r ∈ W'.toValuationSubring) :
    ∃ c : A, W.HasValue r (c : AlgebraicClosure ℚ) ∧
      (P.redFst W).HasValue (R.residue₁ ⟨r, h₁⟩) (red c) := by sorry
