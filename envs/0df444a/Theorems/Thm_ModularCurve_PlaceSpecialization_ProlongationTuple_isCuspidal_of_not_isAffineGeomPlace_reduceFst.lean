-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/e4a772ca-8967-5916-aa4d-ed851dd6ee50
-- title:
--   Non-affine first reduction forces cuspidality of V
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a positive integer $N$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$. Fix further `data`, a `ModularPolynomialData q`, i.e. a monic $\Phi\in\mathbb{Z}[X][Y]$ of degree $\psi(q)=\sum_{d\mid q,\ d\text{ squarefree}}q/d$ in $Y$ with $\Phi$ vanishing when $X$ is evaluated at the $q$-expansion $j$ and $Y$ at the series `jqN q`; a hypothesis `hKr` asserting the Kronecker congruence, namely that reducing $\Phi$ coefficientwise modulo $q$ gives $(C(X)^q-X)\,(C(X)-X^q)$; and hypotheses `hα`, `hβ` asserting that the two maps `heckeAlphaBar` (the inclusion of the level-$N$ function field, base changed to $\overline{\mathbb{Q}}$, into the level-$Nq$ one) and `heckeBetaBar` (the same inclusion twisted by the substitution $q\mapsto q^{q}$ on Laurent series) are integral. Let $P$ be a `PlaceSpecialization` packet for these data, whose first component `P.sp` sends places of the level-$N$ field over $\overline{\mathbb{Q}}$ to places of $\mathrm{modularFunctionFieldC}\ k\ N$, compatibly with $j$ and $j_N$ through $\mathrm{red}$. Let $V$ be a place of the level-$Nq$ field over $\overline{\mathbb{Q}}$ and suppose that `P.reduceFst V`, the image under `P.sp` of the restriction of $V$ along `heckeAlphaBar`, is not affine: at least one of the two generators `jqModC k`, `jqNModC k N` fails to lie in its valuation subring. Then $V$ is cuspidal, that is, $\mathrm{ord}_V\bigl(j-a\bigr)\le 0$ for every $a\in A$, where $j$ denotes the coefficientwise embedding of the $q$-expansion of $j$ into the level-$Nq$ field.
--
--   This is the criterion identifying, on the level-$Nq$ curve, the places lying over the cusps: a place at which $j$ assumes no value in $A$, stated in the contrapositive form that an $A$-integral value of $j$ upstairs would make the first level-$N$ reduction an affine place of the special fibre. It feeds the analysis of the charts of the special fibre of $X_0(Nq)$, in particular the separation of the zero chart from the chart at infinity and the cusp laws for the prolongation tuples.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_isCuspidal_of_not_isAffineGeomPlace_reduceFst.lean

import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.isCuspidal_of_not_isAffineGeomPlace_reduceFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    (hV : ¬ IsAffineGeomPlace k N (P.reduceFst V)) :
    ProlongationTuple.IsCuspidal P V := by sorry
