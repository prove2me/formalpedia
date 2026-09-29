-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residueFst_ne_zero_iff_exists_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/df920dbd-b38d-5297-8507-9405bb812b73
-- title:
--   Nonvanishing residue at the first prolongation as a quotient of primitive expansions
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$ (an algebraic closure of $\mathbb Q$), a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$. Fix modular polynomial data for $q$, that is a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ killing the pair of $q$-expansions, together with a proof $hKr$ that its bivariate reduction modulo $q$ equals $(C(X)^q-X)(C(X)-X^q)$, and proofs $h\alpha,h\beta$ that the two Hecke maps $\alpha,\beta$ at level $1$ and prime $q$ are integral ring homomorphisms over $\overline{\mathbb Q}$. Let $P$ be a place specialisation for these data with residue map $\mathrm{red}$, let $R$ be a level-one prolongation pair for $P$, with first regular prolongation $R_1$, a valuation subring $R_1.\mathrm{integers}$ of the base-changed full modular function field $\overline{\mathbb Q}\cdot F^{\mathrm{full}}_{1\cdot q}\subseteq \overline{\mathbb Q}((\mathfrak q))$ together with its surjective residue homomorphism onto $\mathrm{modularFunctionFieldFullC}\,(\mathrm{ResidueField}\,A)\,1$, and let $f$ be an element of that function field. The assertion is: $f$ lies in $R_1.\mathrm{integers}$ and its residue under $R$.`residue₁` is nonzero if and only if there are Laurent series $x,y$ with coefficients in $A$ such that the coefficientwise reductions $\mathrm{red}(x)$ and $\mathrm{red}(y)$ are both nonzero in $k((\mathfrak q))$ and $f\cdot y=x$ in $\overline{\mathbb Q}((\mathfrak q))$, where $x,y$ are read via the coefficientwise inclusion $A\hookrightarrow\overline{\mathbb Q}$.
--
--   This is the unit criterion for the Gauss-type valuation ring at the cusp of the first prolongation: the elements with nonzero residue are exactly the quotients of two $A$-integral $\mathfrak q$-expansions that are both primitive, i.e. nonzero modulo the maximal ideal of $A$. It sharpens the membership criterion [`ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integersFst_iff_exists_quotient`](thm.html#ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integersFst_iff_exists_quotient), which it cites together with the identification of $R_1.\mathrm{integers}$ with the localised modular ring, and is used by the chart computations for the multiplicative covering at $\infty$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residueFst_ne_zero_iff_exists_quotient
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (f : ↥(modularFunctionFieldBar (1 * q))) :
    (∃ h : f ∈ R.R₁.integers, R.residue₁ ⟨f, h⟩ ≠ 0) ↔
      ∃ x y : LaurentSeries A, coeffMap red x ≠ 0 ∧ coeffMap red y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by sorry
