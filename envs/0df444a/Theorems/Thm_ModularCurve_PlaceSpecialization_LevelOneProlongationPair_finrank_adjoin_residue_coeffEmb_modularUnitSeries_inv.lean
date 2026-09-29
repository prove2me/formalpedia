-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/2273d00e-287f-50bc-9622-25d9fd6ceb0a
-- title:
--   Residue of the modular unit has inverse of degree q-1
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$; fix data $\Phi$ for the modular equation of level $q$ (a monic bivariate integral polynomial of degree $\psi(q)$ vanishing on $(j, j_q)$) whose reduction modulo $q$ satisfies the Kronecker congruence $(Y^q - X)(Y - X^q)$, and integrality hypotheses $h\alpha$, $h\beta$ for the two Hecke maps $\bar\alpha$, $\bar\beta$ at level $1$ and prime $q$. Let $P$ be a place specialisation of level $1$ for these data, and let $R$ be a level-one prolongation pair for $P$: it provides a homomorphism $\overline{red}$ from the residue field of $A$ to $k$ lifting $red$, a coefficientwise map $\iota$ along $\overline{red}$, and two regular prolongations $R_1$, $R_2$ of $A$ from $\overline{\mathbb Q}$ to the function field $\overline{\mathbb Q}\cdot F^{\mathrm{full}}_{1\cdot q}$, each with residue field $\kappa(A)$-rational function field `modularFunctionFieldFullC (ResidueField A) 1`, together with the compatibilities of their residue maps with coefficientwise reduction, with the Fricke involution, and with the localized reduction map. Assume the element $u$ of $\overline{\mathbb Q}\cdot F^{\mathrm{full}}_{1\cdot q}$ whose $q$-expansion is `modularUnitSeries (1 * q)` $= \Delta/\Delta_{(q)}$, pushed along the coefficient embedding, lies in `R.R₁.integers`. Then the field `modularFunctionFieldFullC (ResidueField A) 1` has rank exactly $q-1$ over the subfield generated over the residue field of $A$ by the inverse of the $R_1$-residue of $u$.
--
--   This is the degree computation for the reduced cuspidal modular unit: the residue of $\Delta/\Delta_{(q)}$ at the first Gauss prolongation generates, after inversion, a subfield of index $q-1$ in the residue function field. It feeds the divisor-law and cuspidal-reduction arguments for level-one prolongation pairs, where a generator of prescribed degree is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv.lean

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

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (h : (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
      ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers) :
    Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1)⁻¹} :
          Set ↥(modularFunctionFieldFullC (ResidueField A) 1)))
      ↥(modularFunctionFieldFullC (ResidueField A) 1) = q - 1 := by sorry
