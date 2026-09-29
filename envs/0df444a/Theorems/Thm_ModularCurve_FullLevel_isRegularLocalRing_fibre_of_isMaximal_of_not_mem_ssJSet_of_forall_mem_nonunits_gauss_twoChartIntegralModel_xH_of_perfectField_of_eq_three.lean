-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_isMaximal_of_not_mem_ssJSet_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH_of_perfectField_of_eq_three
-- name    : ModularCurve.FullLevel.isRegularLocalRing_fibre_of_isMaximal_of_not_mem_ssJSet_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH_of_perfectField_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/b2298777-c4de-5539-a4c1-02685b656bef
-- title:
--   Regular special fibre at ordinary ∞-branch points, q=3
-- statement:
--   Fix a prime $q$ with $q=3$ and an integer $M'\ge 1$ with $q\nmid M'$. Let $L$ be a field of characteristic zero, algebraic over $\mathbb{Q}$, containing a primitive $q$-th root of unity $\zeta$ for which some ring homomorphism $\iota:L\to\mathbb{C}$ satisfies $\iota\zeta=\exp(2\pi i/q)$. Let $K\subseteq L((T))$ be the intermediate field obtained by adjoining to $L$ the coefficientwise image, under $\mathbb{Q}\to L$, of the $q$-expansion function field of $X_H$ of level $q^2M'$ with $H=\ker\big((\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times\big)$. Let $A$ be a discrete valuation domain with fraction field $L$, perfect residue field, uniformiser $\varpi$ (so $\mathfrak{m}_A=(\varpi)$), with $q\in\mathfrak{m}_A$ and $\zeta$ in the image of $A$, and let $K$ be an $A$-algebra compatibly with $L$. Let $j\in K$ be nonzero with Laurent expansion the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular invariant. Let $W_0$ be the valuation subring of $K$ consisting of those $f$ expressible as $x/y$ with $x,y\in A[[T]]$ and $y$ nonzero modulo $\mathfrak{m}_A$ (the Gauss valuation ring). Write $\mathfrak{X}=$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the pushout of the two charts $\operatorname{Spec}$ of the integral closures of $A[j]$ and $A[j^{-1}]$ in $K$ along the middle chart. Let $z\in\mathfrak{X}$, let $\varpi_z$ be the germ at $z$ of the global function obtained from $\varpi$ via $\mathfrak{X}\to\operatorname{Spec} A$, and assume $\varpi_z$ lies in the maximal ideal of the stalk $\mathcal{O}_{\mathfrak{X},z}$. Assume $z$ is the image of a point $y$ of the $j$-finite chart $\operatorname{Spec}$ of `chartAlgFin A K j` whose prime ideal is maximal, that there is a ring homomorphism $\varphi$ from that chart algebra to an algebraically closed field $\Omega$ of characteristic $q$ with kernel $y$ and with $\varphi(j)\notin$ [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), i.e. some elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(j)$ has a nonzero point killed by $q$, and that every element of the chart algebra lying in the non-units of $W_0$ belongs to $y$. Then $\mathcal{O}_{\mathfrak{X},z}/(\varpi_z)$ is a regular local ring.
--
--   This is the $q=3$ case of the regularity of the special fibre of the two-chart integral model of $X(\Gamma(q)\cap\Gamma_0(M'))$ at those closed points of the $j$-finite chart that have ordinary $j$-invariant and lie on the branch cut out by the Gauss valuation (the $\infty$-Igusa component). It feeds the construction of an open subscheme on which the map to $\operatorname{Spec} A$ is smooth, and the regularity statement at good points of the integral model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_isMaximal_of_not_mem_ssJSet_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH_of_perfectField_of_eq_three.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.FullLevel.isRegularLocalRing_fibre_of_isMaximal_of_not_mem_ssJSet_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH_of_perfectField_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))

    [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)

    [PerfectField (IsLocalRing.ResidueField A)]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z)
    (hmax : y.asIdeal.IsMaximal)
    (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω)
    (hφ : RingHom.ker φ = y.asIdeal)
    (hord : φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∉ ModularCurve.ssJSet q Ω)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal) :
    IsRegularLocalRing (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ⧸ Ideal.span {ϖz}) := by sorry
