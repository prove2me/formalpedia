-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_exists_two_primes_chartAlgFin_le_asIdeal_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.exists_two_primes_chartAlgFin_le_asIdeal_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/a63ab252-9fec-53e2-9737-c7107d897b47
-- title:
--   Two special-fibre components through a supersingular point
-- statement:
--   Fix a prime $q$, a nonzero $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, let $\zeta \in L$ be a primitive $q$-th root of unity, $\xi \in L$ a primitive $q\ell$-th root of unity with $\zeta = \xi^{\ell}$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the group of units congruent to $1$ both modulo $q$ and modulo $\ell$, i.e. the intersection of the kernels of the reductions $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$ and $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell)^\times$, and let $K \subseteq L((T))$ be the intermediate field generated over $L$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$ inside $\mathbb{Q}((T))$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, with $\zeta$ in the image of $A$, with $K$ an $A$-algebra compatibly with $A \to L \to K$, and let $\varpi$ generate the maximal ideal of $A$. Let $j \in K$ be nonzero with image the coefficientwise image of the rational $j$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Let $z$ be a point of the two-chart integral model [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) (the pushout of the two chart charts over the middle chart) at which the germ of the global section obtained from $\varpi$ along the structure morphism to $\operatorname{Spec} A$ lies in the maximal ideal of the stalk, and let $y$ be a point of $\operatorname{Spec} C$, where $C =$ `chartAlgFin A K j` is the algebra of elements of $K$ integral over $A[j]$, with `ιFin` carrying $y$ to $z$. Assume $y$ is supersingular: for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel the prime of $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), the set of those $j_0$ such that every elliptic Weierstrass curve over $\Omega$ with invariant $j_0$ has no nonzero point killed by $q$. The conclusion is that there exist two distinct prime ideals $G \ne G'$ of $C$, both containing the image of $\varpi$, both contained in the prime of $y$ and both different from it.
--
--   This is the statement that at least two irreducible components of the special fibre $\operatorname{Spec}(C/\varpi C)$ of the $j$-finite chart pass through every supersingular point, in the auxiliary $\Gamma_1(\ell)$-rigidified full-level setting with $q$ arbitrary (in particular $q \in \{2,3\}$ is allowed). It is used to show that the quotient of the stalk at such a point is a discrete valuation ring, in the analysis of the integral model of the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_exists_two_primes_chartAlgFin_le_asIdeal_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd.lean

import Mathlib
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

theorem ModularCurve.FullLevel.AuxLevelOne.exists_two_primes_chartAlgFin_le_asIdeal_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hζξ : ζ = ξ ^ ℓ)
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
    ∃ G G' : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
      G.IsPrime ∧ G'.IsPrime ∧ G ≠ G' ∧
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ G ∧
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ G' ∧
      G ≤ y.asIdeal ∧ G' ≤ y.asIdeal ∧ G ≠ y.asIdeal ∧ G' ≠ y.asIdeal := by sorry
