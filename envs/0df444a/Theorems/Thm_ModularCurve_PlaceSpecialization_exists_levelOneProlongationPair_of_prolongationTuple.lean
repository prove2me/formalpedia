-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_levelOneProlongationPair_of_prolongationTuple
-- name    : ModularCurve.PlaceSpecialization.exists_levelOneProlongationPair_of_prolongationTuple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/2a066221-0e83-5c75-a407-d1d0f28c6b36
-- title:
--   Level-one prolongation tuples give prolongation pairs
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix also modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the $q$-th modular $j$-pair), a witness `hKr` that the bivariate reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$, and witnesses `hα`, `hβ` that the two Hecke homomorphisms $\bar\alpha$, $\bar\beta$ at level $1$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral. Let $P$ be a place specialization for these data at level $N = 1$, and let $R$ be a prolongation tuple over $P$: a lift $\overline{\mathrm{red}}$ of $\mathrm{red}$ through the residue map of $A$, a coefficientwise embedding $\iota$ of the level-$1$ modular function field over the residue field of $A$ into that over $k$, two regular prolongations $R_1, R_2$ of $A$ to $\overline{M}_{1\cdot q}$ with residue field the level-$1$ field over $\mathrm{ResidueField}\,A$, the Gauss property of $R_1$ on Laurent series with coefficients in $A$, the two-sided dictionaries describing membership in $R_1$, respectively $R_2$ (the latter through the partial Atkin–Lehner map `atkinLehnerBar`), by membership of the Laurent series in `CharPReduction.modularLocalized`, and the compatibility of the residues of $R_2$ and $R_1$ and of $\iota \circ R_1$-residue with `modularRedLocHom`. The assertion is that there exists a level-one prolongation pair $R'$ over $P$ — the analogous package in which membership in $R'_2$ is characterised by membership of the Fricke involute in $R'_1$, the residue of $R'_2$ is the residue of $R'_1$ at the Fricke involute, and only the implication from `modularLocalized` to integrality for $R'_1$ is required — with $R'.R_1 = R.R_1$ and $R'.R_2 = R.R_2$.
--
--   This is the comparison, at level $N = 1$, between the prolongation data attached to a place specialization in the general shape and the level-one shape, in which the partial Atkin–Lehner map is the Fricke involution of the level-$q$ function field and only one direction of the integrality dictionary is retained. It lets results proved for level-one prolongation pairs, such as the one-sided cusp laws at $0$ and $\infty$ and the ordinary bounds for residues of models, be applied to prolongation tuples.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_levelOneProlongationPair_of_prolongationTuple.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.exists_levelOneProlongationPair_of_prolongationTuple
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : ProlongationTuple P) :
    ∃ R' : P.LevelOneProlongationPair, R'.R₁ = R.R₁ ∧ R'.R₂ = R.R₂ := by sorry
