-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_coeffEmb_modularUnitSeries_ne_zero
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_coeffEmb_modularUnitSeries_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/f4354b04-56d7-53a5-8a8c-218edf32f22c
-- title:
--   Nonvanishing residue of the modular unit at the first prolongation
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Let `data` be a modular polynomial datum for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions $j$, $j(q\cdot)$) satisfying the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q)$ modulo $q$, and let $h\alpha$, $h\beta$ assert that the two Hecke correspondence maps `heckeAlphaBar`, `heckeBetaBar` at level $1$ and prime $q$ are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` of $A$ at $q$ in level $1$ for these data and $\mathrm{red}$, and let $R$ be a level-one prolongation pair for $P$; among its components are two regular prolongations $R_1$, $R_2$ of $A$ to the field $\overline{\mathbb Q}\cdot F^{\mathrm{full}}_{1\cdot q}$ of Laurent series, with residue field $\mathrm{modularFunctionFieldFullC}(\kappa(A), 1)$. Consider the modular unit $\Delta/\Delta(q\cdot) \in F^{\mathrm{full}}_{1\cdot q}$, viewed in $\overline{\mathbb Q}\cdot F^{\mathrm{full}}_{1\cdot q}$ by coefficientwise extension of scalars along $\mathbb Q \to \overline{\mathbb Q}$. Assuming it lies in the valuation subring $R_1.\mathrm{integers}$, its residue under $R_1.\mathrm{residue}$ is nonzero.
--
--   Since the kernel of the residue map of a regular prolongation is the maximal ideal of its valuation subring, this says that the $\Delta$-quotient modular unit of $X_0(q)$ is a unit at the first of the two prolongations of $A$, i.e. its divisor is supported away from that place. It is used in the computation of the divisor of this unit at the first prolongation, in the Fricke-involution comparison of the two prolongations, and in the ordinary/strict-type-one case analysis at a specialised place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_coeffEmb_modularUnitSeries_ne_zero.lean

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

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_coeffEmb_modularUnitSeries_ne_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (h : (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
      ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers) :
    R.R₁.residue ⟨_, h⟩ ≠ 0 := by sorry
