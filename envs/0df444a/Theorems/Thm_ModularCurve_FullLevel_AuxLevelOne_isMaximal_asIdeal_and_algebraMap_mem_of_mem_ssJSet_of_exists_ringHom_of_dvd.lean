-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_exists_ringHom_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_exists_ringHom_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/7bea6e80-3447-53f9-ad97-ce8ff930a96c
-- title:
--   Supersingular chart points are closed and contain varpi
-- statement:
--   Fix primes $q$ and $\ell$, and $M'\neq 0$ with $q\nmid M'$, $\ell\mid M'$ and $\ell\equiv 11\pmod{12}$. Let $L$ be a field of characteristic $0$ containing a primitive $q$-th root of unity $\zeta$, and assume some ring homomorphism $\iota:L\to\mathbb C$ sends $\zeta$ to $e^{2\pi i/q}$. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of reduction to $(\mathbb Z/q)^\times$, with the kernel of reduction to $(\mathbb Z/\ell)^\times$, and let $K\subset L((\mathsf q))$ be the intermediate field generated over $L$ by the coefficientwise image under $\mathbb Q\to L$ of the $q$-expansion function field [`ModularCurve.xHFunctionField (q ^ 2 * M') H₁`](def/ModularCurve_XH.html#L79). Let $A$ be a discrete valuation ring with fraction field $L$ and algebraically closed residue field, with $q\in\mathfrak m_A=(\varpi)$ and $\zeta$ in the image of $A$, and let $K$ be an $A$-algebra compatibly with $L$. Let $j\in K$ be nonzero with $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), and let $\mathfrak X=$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) be the pushout of the spectra of the integral closures of $A[j]$ and $A[j^{-1}]$ in $K$. Let $z\in\mathfrak X$ be a point at which the image $\varpi_z$ of $\varpi$ under $\mathfrak X\to\operatorname{Spec}A$ and the germ map at $z$ lies in the maximal ideal of the stalk, and let $y$ be a point of $\operatorname{Spec}$ of the $j$-finite chart algebra `chartAlgFin` mapping to $z$. Assume that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from `chartAlgFin` to $\Omega$ with kernel the prime of $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of $a\in\Omega$ such that every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $a$ has no nonzero point killed by $q$. Then the prime of $y$ is maximal, and it contains the image of $\varpi$ under $A\to$ `chartAlgFin`.
--
--   This is the local statement that a point of the $j$-finite chart of the two-chart integral model whose geometric $j$-values are supersingular lies on the special fibre and is a closed point, the $j$-coordinate then being algebraic over $\mathbb F_q$ because $j^{q^2}=j$ holds on supersingular values. It feeds the subsequent identification of the completed stalks at such points with Drinfeld-type charts and the inertia computations at the guard prime $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_exists_ringHom_of_dvd.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevelOne.isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_exists_ringHom_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [IsAlgClosed (IsLocalRing.ResidueField A)]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
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
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
      RingHom.ker φ = y.asIdeal →
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω) :
    y.asIdeal.IsMaximal ∧
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal := by sorry
