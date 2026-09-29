-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersFst
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coeffEmb_modularUnitSeries_mem_integersFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/72186e40-7d11-5f88-b4ba-eecff5979e53
-- title:
--   R₁-integrality of the modular unit with coefficientwise residue
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Fix modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions) together with the Kronecker congruence $hKr$, asserting that $\Phi$ reduces modulo $q$ to $(C\,X^{q}-X)(C\,X-X^{q})$, and hypotheses $h\alpha$, $h\beta$ that the ring homomorphisms `heckeAlphaBar` and `heckeBetaBar` over $\overline{\mathbb Q}$ at level $1$ and prime $q$ are integral. Let $P$ be a place specialisation of this data at level $N=1$, and let $R$ be a level-one prolongation pair for $P$; in particular $R$ provides a regular prolongation $R.R_1$ of $A$ to the field $\overline{\mathbb Q}\cdot F^{\mathrm{full}}_{1\cdot q}$ of Laurent series, with residue map onto `modularFunctionFieldFullC (ResidueField A) 1`. Let $u$ be the element of $\overline{\mathbb Q}\cdot F^{\mathrm{full}}_{1\cdot q}$ obtained by pushing the Laurent series $\Delta \cdot \Delta_{1\cdot q}^{-1}$ forward coefficientwise along $\mathbb Q \to \overline{\mathbb Q}$. The assertion is that $u$ lies in $R.R_1$'s valuation subring of integers, and that there is a Laurent series $y$ with coefficients in $A$ whose coefficientwise image in $\overline{\mathbb Q}((\mathfrak q))$ is the expansion of $u$ and such that the $R_1$-residue of $u$, read as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$.
--
--   The series $\Delta(\mathfrak q)/\Delta(\mathfrak q^{q})$ is the standard modular unit on $X_0(q)$, supported at the two cusps; this statement records that it is integral at the first of the two Gauss prolongations attached to a level-one prolongation pair, with residue computed coefficientwise from an $A$-integral model of its $q$-expansion. It feeds the computation of the divisor of this unit and the analysis of strict type one places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersFst.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coeffEmb_modularUnitSeries_mem_integersFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair) :
    ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
      ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers,
      ∃ y : LaurentSeries A, coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)) ∧
        ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) :
            LaurentSeries (ResidueField A)) = coeffMap (IsLocalRing.residue A) y := by sorry
