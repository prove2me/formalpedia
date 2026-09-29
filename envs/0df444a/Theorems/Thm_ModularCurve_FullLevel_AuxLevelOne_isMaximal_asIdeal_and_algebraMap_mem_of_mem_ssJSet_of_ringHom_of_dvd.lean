-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_ringHom_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_ringHom_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/408b965c-bd9e-542e-a1ed-1ed48cb87d3d
-- title:
--   Supersingular points of the j-finite chart are closed
-- statement:
--   Let $q$ be a prime and $M'$ a non-zero natural number with $q \nmid M'$, and let $\ell$ be a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero containing a primitive $q$-th root of unity $\zeta$, and assume there is a ring homomorphism $L \to \mathbb{C}$ sending $\zeta$ to $\exp(2\pi i/q)$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$ with the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell)^\times$, that is, the units congruent to $1$ modulo $q$ and modulo $\ell$. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ generated over $L$ by the image, under the coefficientwise map induced by $\mathbb{Q} \to L$, of the function field [`ModularCurve.xHFunctionFieldC`](def/ModularCurve_XH.html#L76) of $\Gamma_{H_1}(q^2M')$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, with $\zeta$ in the image of $A \to L$, and with uniformiser $\varpi$ generating the maximal ideal; $K$ is an $A$-algebra compatibly with $A \to L \to K$. Let $j \in K$ be non-zero with Laurent expansion the image of the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular $j$-function, and write $C =$ `chartAlgFin A K j` for the integral closure of $A[j]$ in $K$, with `jChartFin` the element $j$ of $C$. Let $z$ be a point of the two-chart integral model [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) (the pushout of $\mathrm{Spec}$ of the two chart algebras along the middle chart), let $\varpi z$ be the germ at $z$ of the global section obtained from $\varpi$ along the structure morphism to $\mathrm{Spec}\,A$, and assume $\varpi z$ lies in the maximal ideal of the local ring at $z$. Let $y$ be a point of $\mathrm{Spec}\,C$ mapping to $z$ under the canonical morphism `ιFin`, and assume that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel the prime $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of $a \in \Omega$ such that every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $a$ has no non-zero point killed by $q$. Then the prime ideal of $y$ is maximal in $C$, and the image of $\varpi$ under $A \to C$ lies in it.
--
--   This identifies a point of the $j$-finite chart whose $j$-invariant is supersingular as a closed point of the special fibre over the discrete valuation ring $A$. It is used in the analysis of the completed local rings of the integral model at supersingular points, in particular in the cyclotomic base-change step and in the comparison of stalks under the Diamond construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_ringHom_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.isMaximal_asIdeal_and_algebraMap_mem_of_mem_ssJSet_of_ringHom_of_dvd
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
