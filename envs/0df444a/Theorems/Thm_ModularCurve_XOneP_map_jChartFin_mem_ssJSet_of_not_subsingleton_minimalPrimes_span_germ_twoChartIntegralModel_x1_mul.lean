-- Prove2me | Theorems.Thm_ModularCurve_XOneP_map_jChartFin_mem_ssJSet_of_not_subsingleton_minimalPrimes_span_germ_twoChartIntegralModel_x1_mul
-- name    : ModularCurve.XOneP.map_jChartFin_mem_ssJSet_of_not_subsingleton_minimalPrimes_span_germ_twoChartIntegralModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/e0e7b7b7-7ec3-5aac-a90d-de80c36b1f87
-- title:
--   Crossing points of the special fibre have supersingular j
-- statement:
--   Fix a prime $p$ and an integer $M \ge 5$ (nonzero) with $p \nmid M$. Let $L$ be a field of characteristic zero which is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$, and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained, as [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103), by adjoining to $L$ the image of the function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) $\subseteq \mathrm{LaurentSeries}\,\mathbb{Q}$ under the coefficientwise map [`ModularCurve.coeffEmb`](def/ModularCurve_LaurentCoeff.html#L81) induced by $\mathbb{Q} \to L$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ lies in the image of $A$, with an $A$-algebra structure on $K$ compatible with that on $L$, and let $\varpi$ generate the maximal ideal of $A$. Let $j \in K$ be nonzero with underlying Laurent series the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) transported to $L$, and let $X =$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) be the pushout glueing $\operatorname{Spec}$ of the $A$-algebra of elements of $K$ integral over $A[j]$ to $\operatorname{Spec}$ of the one of elements integral over $A[j^{-1}]$, with structure morphism `toBase` to $\operatorname{Spec} A$. Let $z \in X$, let $\varpi_z$ be the germ at $z$ of the image of $\varpi$ under `toBase` on global sections, assume $\varpi_z$ lies in the maximal ideal of the stalk $\mathcal{O}_{X,z}$, assume $z$ is the image under `ιFin` of a point $y$ of the finite chart $\operatorname{Spec}$ `chartAlgFin`, and assume the ideal $(\varpi_z) \subseteq \mathcal{O}_{X,z}$ has at least two minimal primes. Finally let $\Omega$ be an algebraically closed field of characteristic $p$ (with decidable equality) and $\varphi :$ `chartAlgFin` $\to \Omega$ a ring homomorphism with kernel the prime of $y$. Then $\varphi(j)$ lies in [`ModularCurve.ssJSet p Ω`](def/ModularCurve_SupersingularModuli.html#L7), i.e. every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(j)$ has no nonzero affine point killed by $p$.
--
--   This is the statement that a point of the special fibre of the two-chart integral model of $X_1(Mp)$ over a discrete valuation ring above $p$ in $\mathbb{Q}(\zeta_p)$ at which two branches cross must have supersingular $j$-invariant; classically the components of $X_1(Mp) \otimes \mathbb{F}_p$ meet precisely above the supersingular points. It is used in the analysis of the irreducible components of the special fibre of the model, feeding the identification of crossing points in that fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_map_jChartFin_mem_ssJSet_of_not_subsingleton_minimalPrimes_span_germ_twoChartIntegralModel_x1_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem ModularCurve.XOneP.map_jChartFin_mem_ssJSet_of_not_subsingleton_minimalPrimes_span_germ_twoChartIntegralModel_x1_mul
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
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hcross : ¬ (Ideal.span {ϖz} :
      Ideal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)).minimalPrimes.Subsingleton)
    (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω)
    (hφ : RingHom.ker φ = y.asIdeal) :
    φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet p Ω := by sorry
