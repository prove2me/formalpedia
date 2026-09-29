-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersFst_iff_exists_quotient
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integersFst_iff_exists_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/aca5ff24-d1ee-5881-a2ca-a89aafcf4521
-- title:
--   R₁-integrality as a quotient of A-integral Laurent series
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A \to k$. Let `data` consist of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, let `hKr` be the hypothesis that its reduction modulo $q$ is $(X^q - Y)(X - Y^q)$ in the bivariate coordinates used, and let `hα`, `hβ` assert that the ring homomorphisms underlying $\overline{\alpha}$ and $\overline{\beta}$ at level $1$ and prime $q$ are integral. Let $P$ be a place specialization of type `PlaceSpecialization A q 1 data hKr k red hα hβ` and $R$ a `LevelOneProlongationPair` for $P$, whose component $R_1$ is a regular prolongation of $A$ to the function field $\overline{\mathbb Q}\cdot F^{\mathrm{full}}_{q}$, realised as an intermediate field `modularFunctionFieldBar (1 * q)` of $\overline{\mathbb Q}(\!(\mathfrak q)\!)$. Then for $f$ in that function field, $f$ lies in the valuation subring $R_1.\mathrm{integers}$ if and only if there are Laurent series $x, y$ with coefficients in $A$ such that the coefficientwise reduction `coeffMap red y` is a nonzero element of $k(\!(\mathfrak q)\!)$ and $f \cdot y = x$ holds in $\overline{\mathbb Q}(\!(\mathfrak q)\!)$, $x$ and $y$ being mapped coefficientwise by the inclusion $A \hookrightarrow \overline{\mathbb Q}$.
--
--   The ring $R_1$ plays the role of the valuation ring of the component of the special fibre of $X_0(q)$ through the cusp $\infty$, and the statement presents its elements concretely as quotients of $A$-integral $q$-expansions whose denominator has nonzero reduction. It is obtained from the dictionary `mem_integersFst_iff_coe_mem_modularLocalized` identifying $R_1$-integrality with membership of the localisation of the modular ring at the kernel of coefficientwise reduction, and is used in the study of the chart at infinity of the multiplicative covering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersFst_iff_exists_quotient.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integersFst_iff_exists_quotient
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (f : ↥(modularFunctionFieldBar (1 * q))) :
    f ∈ R.R₁.integers ↔
      ∃ x y : LaurentSeries A, coeffMap red y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by sorry
