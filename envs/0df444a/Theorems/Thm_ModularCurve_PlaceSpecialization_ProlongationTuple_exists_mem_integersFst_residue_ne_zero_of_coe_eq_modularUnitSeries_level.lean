-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/ceb79a7e-3235-5161-b9eb-09aefb95858b
-- title:
--   Modular unit Δ/Δ_q: R₁-integral, residue of order 1-q
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ (the algebraic closure of $\mathbb{Q}$ used throughout), a nonzero level $N$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Fix moreover data $\Phi$ for the modular equation of level $q$ (a monic polynomial in $\mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions), a proof `hKr` that its reduction modulo $q$ equals $(C X^q - X)(C X - X^q)$, and proofs `hα`, `hβ` that the two Hecke maps `heckeAlphaBar`, `heckeBetaBar` at level $N$ and prime $q$ are integral ring homomorphisms. Let $P$ be a place specialisation attached to these data and $R$ a prolongation tuple over $P$, so in particular $R$ provides two regular prolongations $R_1$, $R_2$ of $A$ to the function field `modularFunctionFieldBar (N * q)` with residue field extension `modularFunctionFieldFullC (ResidueField A) N`. Let $u$ be an element of `modularFunctionFieldBar (N * q)` whose $q$-expansion is the coefficientwise image in $\overline{\mathbb{Q}}$-Laurent series of `modularUnitSeries q`, the series $\Delta \cdot \Delta_q^{-1}$. Then $u$ lies in the valuation subring $R_1$.`integers`; its residue under $R_1$.`residue` is nonzero; and there is a Laurent series $y$ with coefficients in $A$ whose image under the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the expansion of $u$, such that the expansion of that residue, viewed as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$ and has order $1 - q$.
--
--   This records the classical modular unit $\Delta/\Delta_q$ on $X_0(Nq)$ as a unit for the first of the two Gauss prolongations attached to a place specialisation, together with the order $1-q$ of its reduced $q$-expansion. It is used in the identification of the behaviour of the two prolongations at the cusps $0$ and $\infty$, including the level-one cusp laws for prolongation tuples.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open HahnSeries ModularCurve AlgebraicCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q)) :
    ∃ h₁ : u ∈ R.R₁.integers,
      R.R₁.residue ⟨u, h₁⟩ ≠ 0 ∧
      ∃ y : LaurentSeries A, coeffMap A.subtype y = (u : LaurentSeries (AlgebraicClosure ℚ)) ∧
        ((R.R₁.residue ⟨u, h₁⟩ : modularFunctionFieldFullC (ResidueField A) N) :
            LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y ∧
        ((R.R₁.residue ⟨u, h₁⟩ : modularFunctionFieldFullC (ResidueField A) N) :
            LaurentSeries (ResidueField A)).order = 1 - (q : ℤ) := by sorry
