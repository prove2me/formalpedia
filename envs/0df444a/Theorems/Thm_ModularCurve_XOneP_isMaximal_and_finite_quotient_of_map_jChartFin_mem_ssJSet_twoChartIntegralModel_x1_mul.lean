-- Prove2me | Theorems.Thm_ModularCurve_XOneP_isMaximal_and_finite_quotient_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul
-- name    : ModularCurve.XOneP.isMaximal_and_finite_quotient_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/c6a0c5a3-3956-56ed-b0be-b574fc7565c1
-- title:
--   Supersingular points of the j-finite chart of X₁(Mp) are closed
-- statement:
--   Fix a prime $p$, an integer $M$ with $M \ge 5$ and $p \nmid M$, a field $L$ of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and a primitive $p$-th root of unity $\zeta \in L$. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained as `laurentBaseChange`, i.e. generated over $L$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_1(Mp)$ over $\mathbb{Q}$ inside $\mathrm{LaurentSeries}\,\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal, with $\zeta$ in the image of $A \to L$, with a compatible $A$-algebra structure on $K$, and let $\varpi$ generate the maximal ideal of $A$. Let $j \in K$ be nonzero with Laurent expansion $q^{-1}\,j_{\mathrm{num}}(q)$, the image of `jq`. Write $A'_{\mathrm{fin}} =$ `chartAlgFin` $A\,K\,j$ for the subalgebra of elements of $K$ integral over $A[j]$, and let $y$ be a point of $\operatorname{Spec} A'_{\mathrm{fin}}$, i.e. a prime $y$ of $A'_{\mathrm{fin}}$, whose ideal contains the image of $\varpi$. Assume that for every algebraically closed field $\Omega$ of characteristic $p$ with decidable equality and every ring homomorphism $\varphi \colon A'_{\mathrm{fin}} \to \Omega$ with kernel exactly $y$, the element $\varphi(j)$ lies in `ssJSet` $p\,\Omega$, the set of $t \in \Omega$ such that every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $t$ has no nonzero affine point killed by $p$. Then $y$ is a maximal ideal and the quotient $A'_{\mathrm{fin}}/y$ is finite.
--
--   This is the statement that a supersingular point of the special fibre of the $j$-finite chart of the integral model of $X_1(Mp)$ is a closed point with finite residue field: non-maximal primes above $\varpi$ are minimal primes of $(\varpi)$, the centres of the two Gauss-type branch valuations, along which the reduction of $j$ is transcendental and hence not supersingular, while for maximal $y$ the quotient is a field of finite type over $\mathbb{F}_p$. It feeds the analysis of the stalks of the two-chart model at supersingular points, in particular the crossing presentation of the stalk, the regularity of the stalk after pullback, and the statement that residue fields do not grow at such points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_isMaximal_and_finite_quotient_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem ModularCurve.XOneP.isMaximal_and_finite_quotient_of_map_jChartFin_mem_ssJSet_twoChartIntegralModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (y : ↥(XFin A (↥K) j))
    (hyϖ : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal)

    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet p Ω) :
    y.asIdeal.IsMaximal ∧ Finite (↥(chartAlgFin A (↥K) j) ⧸ y.asIdeal) := by sorry
