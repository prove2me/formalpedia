-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_mem_asIdeal_of_coe_mem_nonunits_gaussValuationSubring_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.mem_asIdeal_of_coe_mem_nonunits_gaussValuationSubring_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/18f20375-d9f0-59db-96c9-1979dc4afd1a
-- title:
--   Gauss non-units lie in supersingular primes of the finite chart
-- statement:
--   Fix a prime $q$ and a nonzero $M'$ with $q \nmid M'$, and a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, let $\zeta \in L$ be a primitive $q$-th root of unity, $\xi \in L$ a primitive $q\ell$-th root of unity, with $\zeta = \xi^{\ell}$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$ with the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell)^\times$, and let $K =$ `laurentBaseChange` $L$ of `xHFunctionField` $(q^2M')\,H_1$, i.e. the intermediate field of $L \subseteq L((X))$ generated over $L$ by the coefficientwise image under `coeffEmb` of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$. Let $A$ be a discrete valuation ring with fraction field $L$, with $q$ in its maximal ideal, with $\zeta$ in the image of $A$, with uniformiser $\varpi$ (so $\mathfrak{m}_A = (\varpi)$), and with an $A$-algebra structure on $K$ compatible with $A \to L \to K$. Let $j \in K$ be nonzero with underlying Laurent series `coeffEmb` $L$ applied to the $q$-expansion `jq` of the modular $j$-function. Consider the two-chart integral model $X =$ `TwoChartIntegralModel` $A\,K\,j$, the pushout of the two spectra of the chart algebras $\mathrm{chartAlgFin} = \{x \in K : x$ integral over $A[j]\}$ and $\mathrm{chartAlgInf}$ over the middle one. Let $z$ be a point of $X$, let $\varpi_z$ be the germ at $z$ of the global function on $X$ obtained from $\varpi$ through the structure morphism $X \to \operatorname{Spec} A$, and assume $\varpi_z$ lies in the maximal ideal of the stalk of $X$ at $z$. Let $y$ be a point of $\operatorname{Spec}(\mathrm{chartAlgFin}\,A\,K\,j)$ mapping to $z$, and assume $y$ is supersingular in the sense that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from $\mathrm{chartAlgFin}\,A\,K\,j$ to $\Omega$ with kernel exactly the prime $y$, the value $\varphi(j)$ lies in `ssJSet` $q\,\Omega$, i.e. every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $\varphi(j)$ has no nonzero point annihilated by $q$. Let $W_0$ be a valuation subring of $K$ consisting exactly of those $f$ for which there are power series $x, y_0$ over $A$ with $y_0$ of nonzero reduction modulo $\mathfrak{m}_A$ and $f \cdot y_0 = x$ as Laurent series over $L$ (the Gauss valuation ring). Then every $h$ in $\mathrm{chartAlgFin}\,A\,K\,j$ whose image in $K$ is a non-unit of $W_0$ lies in the prime ideal $y$.
--
--   This is the local statement that at a supersingular point of the special fibre of the two-chart integral model of $X_{H_1}(q^2M')$ the maximal ideal of the Gauss valuation ring is carried into the corresponding prime of the finite chart algebra, in the auxiliary level setting where the full auxiliary level is replaced by the $\Gamma_1(\ell)$ condition for a guard prime $\ell \equiv 11 \pmod{12}$. It is used by [`ModularCurve.FullLevel.AuxLevelOne.exists_two_primes_chartAlgFin_le_asIdeal_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd`](thm.html#ModularCurve.FullLevel.AuxLevelOne.exists_two_primes_chartAlgFin_le_asIdeal_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_mem_asIdeal_of_coe_mem_nonunits_gaussValuationSubring_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.mem_asIdeal_of_coe_mem_nonunits_gaussValuationSubring_of_mem_ssJSet_twoChartIntegralModel_of_isPrimitiveRoot_mul_of_dvd
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
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω)

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hh : ((h : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) ∈ W₀.nonunits) :
    h ∈ y.asIdeal := by sorry
