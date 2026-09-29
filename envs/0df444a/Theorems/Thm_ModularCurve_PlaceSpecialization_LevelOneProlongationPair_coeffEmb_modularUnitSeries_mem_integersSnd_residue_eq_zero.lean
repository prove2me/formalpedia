-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersSnd_residue_eq_zero
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coeffEmb_modularUnitSeries_mem_integersSnd_residue_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/775dd19a-39a7-5cb4-8970-8e0fa84e2475
-- title:
--   Vanishing of the modular unit's second residue at level one
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$. Fix further a datum `data : ModularPolynomialData q`, that is a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions, satisfying the Kronecker congruence `hKr`, namely that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)(C(X) - X^q)$; fix hypotheses `hα`, `hβ` asserting that the two Hecke correspondence maps $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ over $\overline{\mathbb Q}$ at level $1$ and prime $q$ are integral ring homomorphisms; and fix a place-specialization datum $P$ for these at level $N = 1$, together with a level-one prolongation pair $R$ for $P$, which in particular provides two regular prolongations $R_1, R_2$ of $A$ to the function field `modularFunctionFieldBar (1 * q)` with residue field `modularFunctionFieldFullC (ResidueField A) 1`, whose integers and residues are related by the Fricke involution. The assertion is that the element of `modularFunctionFieldBar (1 * q)` obtained by coefficientwise base change to $\overline{\mathbb Q}$ of the modular unit series $\Delta \cdot \Delta_{q}^{-1}$ lies in the valuation subring $R_2$.integers, and that its residue under $R_2$.residue is $0$.
--
--   This records, in the prolongation-pair formalism, the classical fact that the cuspidal unit $\Delta(\mathfrak q)/\Delta(\mathfrak q^{q})$ on $X_0(q)$ is integral along the second Gauss prolongation and vanishes identically on the corresponding component of the special fibre. It feeds the case analysis on the behaviour of the modular unit and its Fricke transform at a fixed ordinary specialization, used in the results on non-negativity of the orders of the first and second residues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersSnd_residue_eq_zero.lean

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

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coeffEmb_modularUnitSeries_mem_integersSnd_residue_eq_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair) :
    ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
      ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₂.integers, R.R₂.residue ⟨_, h⟩ = 0 := by sorry
