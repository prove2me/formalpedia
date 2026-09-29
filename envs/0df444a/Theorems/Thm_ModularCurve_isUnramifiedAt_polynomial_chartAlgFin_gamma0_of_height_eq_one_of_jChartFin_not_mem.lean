-- Prove2me | Theorems.Thm_ModularCurve_isUnramifiedAt_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_jChartFin_not_mem
-- name    : ModularCurve.isUnramifiedAt_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_jChartFin_not_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/1e9a5548-c1fa-570e-9c05-1956a5935c8b
-- title:
--   Unramifiedness of A[j₀]→ B₀ at horizontal primes avoiding 0,1728
-- statement:
--   Fix $M'\ge 1$ and a field $L$ of characteristic zero that is algebraic over $\mathbb{Q}$. Let $K_0$ be an intermediate field of the Laurent series field $L(\!(q)\!)$ over $L$, assumed equal to [`ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))`](def/ModularCurve_LaurentCoeff.html#L103): that is, $K_0$ is generated over $L$ by the coefficientwise images in $L(\!(q)\!)$ of the subfield of $\mathbb{Q}(\!(q)\!)$ generated over $\mathbb{Q}$ by the quotients $\mathrm{int}(p_f)/\mathrm{int}(p_g)$ of integral $q$-expansions of modular forms $f,g$ of equal weight for $\Gamma_0(M')$ (with $\mathrm{int}(p_g)\neq 0$). Let $A$ be a discrete valuation ring that is a domain with fraction field $L$, equipped with an algebra structure on $K_0$ compatible with $A\to L\to K_0$, and let $\varpi\in A$ generate the maximal ideal. Let $j_0\in K_0$ be an element whose image in $L(\!(q)\!)$ is the coefficient embedding of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) $=q^{-1}\cdot j_{\mathrm{num}}$, the rational $q$-expansion of the modular invariant, and assume $j_0\neq 0$. Write $B_0=$ [`AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A K₀ j₀`](def/AlgebraicCurve_TwoChartIntegralModel.html#L142) for the subalgebra of elements of $K_0$ integral over $A[j_0]=$ `Algebra.adjoin A {j₀}`, and let $\mathfrak{Q}\subseteq B_0$ be a prime ideal of height one with $\varpi\notin\mathfrak{Q}$, $j_0\notin\mathfrak{Q}$ and $j_0-1728\notin\mathfrak{Q}$. Then, for the $A[X]$-algebra structure on $B_0$ given by $X\mapsto j_0$ (the map `polynomialToChartFin`, i.e. evaluation of polynomials at $j_0$), the algebra $A[X]\to B_0$ is unramified at $\mathfrak{Q}$.
--
--   This is the arithmetic form of the statement that the covering $X_0(M')\to X(1)$ of the $j$-line is unramified, in characteristic zero, at points whose $j$-invariant avoids $0$, $1728$ and $\infty$, the ramification of $j$ on a modular curve occurring only at elliptic points and cusps; the height-one condition together with $\varpi\notin\mathfrak{Q}$ selects the horizontal primes. It feeds the analysis of primes of the integral model at full level, being used in [`ModularCurve.FullLevel.existsUnique_prime_le_jChartFin_sub_mem_map_sup_span_eq_maximalIdeal_chartAlgFin_gamma0_of_not_dvd`](thm.html#ModularCurve.FullLevel.existsUnique_prime_le_jChartFin_sub_mem_map_sup_span_eq_maximalIdeal_chartAlgFin_gamma0_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isUnramifiedAt_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_jChartFin_not_mem.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.isUnramifiedAt_polynomial_chartAlgFin_gamma0_of_height_eq_one_of_jChartFin_not_mem
    (M' : ℕ) [NeZero M']
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀)) [𝔔.IsPrime] (h𝔔 : 𝔔.height = 1)
    (hϖ𝔔 : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) ϖ ∉ 𝔔)
    (hj𝔔 : AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K₀) j₀ ∉ 𝔔)
    (hj𝔔' : AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K₀) j₀ - 1728 ∉ 𝔔) :
    letI : Algebra (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K₀) j₀) :=
      (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin A (↥K₀) j₀).toRingHom.toAlgebra
    Algebra.IsUnramifiedAt (Polynomial A) 𝔔 := by sorry
