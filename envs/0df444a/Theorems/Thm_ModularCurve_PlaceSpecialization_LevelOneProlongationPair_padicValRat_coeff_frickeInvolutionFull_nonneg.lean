-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_padicValRat_coeff_frickeInvolutionFull_nonneg
-- name    : ModularCurve.PlaceSpecialization.LevelOneProlongationPair.padicValRat_coeff_frickeInvolutionFull_nonneg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/cfd28cf1-36ec-53e1-863e-d8f523af88f9
-- title:
--   q-integrality of coefficients of the Fricke transform
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ which is algebraically closed, and a ring homomorphism $\mathrm{red} : A \to k$. Fix further modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions), a proof `hKr` that $\Phi$ reduced mod $q$ factors as $(X^q - Y)(X - Y^q)$ in the relevant bivariate sense, proofs $h\alpha$, $h\beta$ that the two Hecke maps $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ at level $1$ and prime $q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms, a place specialisation $P$ of type `PlaceSpecialization A q 1 data hKr k red hα hβ`, and a level-one prolongation pair $R$ for $P$ (a pair of regular prolongations $R_1$, $R_2$ of $A$ to $\mathrm{modularFunctionFieldBar}(1\cdot q)$ exchanged by the Fricke involution, together with residue data compatible with $\mathrm{red}$). Let $g$ lie in $\mathrm{modularFunctionFieldFull}(1\cdot q)$, the subfield of $\mathbb Q(\!(\mathfrak q)\!)$ generated over $\mathbb Q$ by the divisor expansions at level $q$. Assume: (i) for every place $W$ of $\mathrm{modularFunctionFieldBar}(1\cdot q)$ over $\overline{\mathbb Q}$ other than $\mathrm{cuspInftyBar}(1\cdot q)$, the order $\mathrm{ord}_W$ of the coefficientwise base change of $g$ along $\mathbb Q \hookrightarrow \overline{\mathbb Q}$ is $\ge 0$; (ii) every Laurent coefficient of $g$ has nonnegative $q$-adic valuation. Then for every $m \in \mathbb Z$ the $m$-th coefficient of the Laurent series underlying $\mathrm{frickeInvolutionFull}(1\cdot q)\,g$ also has nonnegative $q$-adic valuation.
--
--   This is a $q$-expansion integrality statement transported across the Fricke involution $w_q$ on $X_0(q)$: a rational function regular away from the cusp $\bar\infty$ with $q$-integral expansion there has $q$-integral expansion after applying $w_q$, i.e. at the other cusp. It is used in the construction of the multiplicity-covering data, in [`ModularCurve.MultCovering.exists_famCtx`](thm.html#ModularCurve.MultCovering.exists_famCtx) and [`ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue`](thm.html#ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue), where a lattice basis adapted to both cusps is produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_padicValRat_coeff_frickeInvolutionFull_nonneg.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.LevelOneProlongationPair.padicValRat_coeff_frickeInvolutionFull_nonneg
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} [IsAlgClosed k] (R : P.LevelOneProlongationPair)
    (g : ↥(modularFunctionFieldFull (1 * q)))
    (hg : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W ≠ cuspInftyBar (1 * q) →
      0 ≤ W.ord (⟨coeffEmb (AlgebraicClosure ℚ) (g : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) g.2⟩ : ↥(modularFunctionFieldBar (1 * q))))
    (hint : ∀ m : ℤ, 0 ≤ padicValRat q ((g : LaurentSeries ℚ).coeff m)) (m : ℤ) :
    0 ≤ padicValRat q (((frickeInvolutionFull (1 * q) g : ↥(modularFunctionFieldFull (1 * q))) :
      LaurentSeries ℚ).coeff m) := by sorry
