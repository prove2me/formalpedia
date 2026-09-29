-- Prove2me | Theorems.Thm_ModularCurve_isSeparable_residueField_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_mem_of_not_dvd
-- name    : ModularCurve.isSeparable_residueField_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_mem_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/859f8862-1c1b-5617-9d7f-90208a54d7a1
-- title:
--   Residue separability over the j-line for X₀(M') when q ∤ M'
-- statement:
--   Fix a prime $q$ and a positive integer $M'$ with $q \nmid M'$, and a field $L$ of characteristic zero that is algebraic over $\mathbb{Q}$. Let $K_0$ be an intermediate field of $L \subseteq L(\!(q)\!)$ which is assumed equal to [`ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the subfield generated over $L$ by the coefficientwise images in $L(\!(q)\!)$ of the elements of the subfield of $\mathbb{Q}(\!(q)\!)$ generated over $\mathbb{Q}$ by all quotients $f/g$ of integral $q$-expansions of modular forms of equal weight for $\Gamma_0(M')$ with $g \neq 0$. Let $A$ be a discrete valuation ring which is an $L$-subring with fraction field $L$, with $q$ in its maximal ideal and $\varpi$ a generator of that maximal ideal, and let $K_0$ be an $A$-algebra compatibly with $L$. Let $j_0 \in K_0$ be a nonzero element whose Laurent series is the coefficientwise image of $q^{-1}\,j_{\mathrm{num}}$, the $q$-expansion of the modular invariant. Write $B_0 =$ [`AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A K₀ j₀`](def/AlgebraicCurve_TwoChartIntegralModel.html#L142), the subalgebra of elements of $K_0$ integral over $A[j_0]$, regarded as an $A[X]$-algebra by the map sending $p$ to $p(j_0)$. Let $\mathfrak{Q} \subset B_0$ be a prime ideal of height one containing the image of $\varpi$, and let $\mathfrak{q} = \mathfrak{Q} \cap A[X]$ be its contraction, the localisations at $\mathfrak{q}$ and $\mathfrak{Q}$ being related by the expected algebra structure. The conclusion is that the residue field extension $\kappa(\mathfrak{q}) \to \kappa(\mathfrak{Q})$ is separable.
--
--   This is the statement that, for residue characteristic $q$ prime to the level $M'$, the special fibre of the integral model of $X_0(M')$ built from the $j$-finite chart is generically separable over the $\bar\jmath$-line: the function field of the special fibre is separable over $\kappa(\bar\jmath)$. It feeds the unramifiedness statement [`ModularCurve.isUnramifiedAt_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_mem_of_not_dvd`](thm.html#ModularCurve.isUnramifiedAt_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_mem_of_not_dvd) for the same vertical prime, used in the good-reduction analysis of modular curves away from the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isSeparable_residueField_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_mem_of_not_dvd.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.isSeparable_residueField_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_mem_of_not_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) [𝔔.IsPrime] (h𝔔 : 𝔔.height = 1)
    (hϖ𝔔 : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ ∈ 𝔔)
    [Algebra (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)]
    (halg : ∀ p : Polynomial A, algebraMap (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) p =
      AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin A (↥K₀) j₀ p)
    [Algebra (Localization.AtPrime (𝔔.under (Polynomial A))) (Localization.AtPrime 𝔔)]
    [Localization.AtPrime.IsLiesOverAlgebra (𝔔.under (Polynomial A)) 𝔔] :
    Algebra.IsSeparable (𝔔.under (Polynomial A)).ResidueField 𝔔.ResidueField := by sorry
