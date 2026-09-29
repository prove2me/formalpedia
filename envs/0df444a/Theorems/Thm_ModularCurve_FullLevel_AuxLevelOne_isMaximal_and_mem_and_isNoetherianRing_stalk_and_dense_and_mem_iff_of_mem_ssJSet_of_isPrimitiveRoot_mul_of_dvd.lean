-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevelOne_isMaximal_and_mem_and_isNoetherianRing_stalk_and_dense_and_mem_iff_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.FullLevel.AuxLevelOne.isMaximal_and_mem_and_isNoetherianRing_stalk_and_dense_and_mem_iff_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/926325f5-d85e-5a94-88de-40d7786313af
-- title:
--   Stalk facts at a supersingular point of the j-finite chart
-- statement:
--   Let $q$ be a prime and $M'$ a nonzero natural number with $q \nmid M'$, and let $\ell$ be a prime with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $L$ be a field of characteristic zero containing a primitive $q$-th root of unity $\zeta$ and a primitive $q\ell$-th root of unity $\xi$ with $\zeta = \xi^{\ell}$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$ (that is, [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the units congruent to $1$ modulo $q$) with the kernel of reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell)^\times$. Let $K$ be the intermediate field of $L((X))$ obtained by adjoining to $L$ the coefficientwise image of the field of $q$-expansions attached to $\Gamma_{H_1}(q^2M')$ over $\mathbb{Q}$. Let $A$ be a discrete valuation ring with fraction field $L$ such that $q$ lies in the maximal ideal of $A$ and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly with $L$; let $\varpi$ generate the maximal ideal of $A$. Let $j \in K$ be nonzero with Laurent expansion the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) of the modular $j$-function transported to $L$. Write $\mathcal{A}$ for the chart algebra `chartAlgFin A K j`, the $A$-subalgebra of elements of $K$ integral over $A[j]$, and $\mathfrak{X} =$ `TwoChartIntegralModel A K j`, the pushout of $\operatorname{Spec}$ of the two chart algebras along the middle scheme. Let $z$ be a point of $\mathfrak{X}$ such that the germ at $z$ of the global section obtained from $\varpi$ along the structure morphism $\mathfrak{X} \to \operatorname{Spec} A$ lies in the maximal ideal of the stalk $\mathcal{O}_{\mathfrak{X},z}$, and let $y$ be a point of $\operatorname{Spec}\mathcal{A}$ mapping to $z$ under `ιFin`, such that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : \mathcal{A} \to \Omega$ with kernel the prime of $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), i.e. every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has no nonzero point killed by $q$. Then, writing $\mathcal{O} = \mathcal{O}_{\mathfrak{X},z}$ and $\mathrm{germY} : \mathcal{A} \to \mathcal{O}$ for the map induced by `ιFin` on the open image of $\operatorname{Spec}\mathcal{A}$: the prime of $y$ is a maximal ideal of $\mathcal{A}$; the image of $\varpi$ in $\mathcal{A}$ lies in it; $\mathcal{O}$ is Noetherian; for every $r \in \mathcal{O}$ and every $n \in \mathbb{N}$ there is $c \in \mathcal{A}$ with $r - \mathrm{germY}(c) \in \mathfrak{m}_{\mathcal{O}}^{\,n}$; and for $c \in \mathcal{A}$ one has $\mathrm{germY}(c) \in \mathfrak{m}_{\mathcal{O}}$ if and only if $c$ lies in the prime of $y$.
--
--   This is the package of local facts at a point of the two-chart integral model of the modular curve lying over a supersingular $j$-invariant in characteristic $q$: closedness of the point on the $j$-finite chart, Noetherianity of the local ring, density of the chart algebra in every $\mathfrak{m}$-adic truncation of the stalk, and the identification of the maximal ideal with the prime of $y$. It is used in the level-$\Gamma_1(\ell)$ auxiliary frame to compute the local behaviour of Galois action on the stalk, in the deduction that a row of the linear part lies in the maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevelOne_isMaximal_and_mem_and_isNoetherianRing_stalk_and_dense_and_mem_iff_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd.lean

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

theorem ModularCurve.FullLevel.AuxLevelOne.isMaximal_and_mem_and_isNoetherianRing_stalk_and_dense_and_mem_iff_of_mem_ssJSet_of_isPrimitiveRoot_mul_of_dvd
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
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
    let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
      ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
          ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
        ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
          (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

    y.asIdeal.IsMaximal ∧
    algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal ∧

    IsNoetherianRing STK ∧

    (∀ (r : STK) (n : ℕ), ∃ c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
      r - germY c ∈ (IsLocalRing.maximalIdeal STK) ^ n) ∧

    (∀ c : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),
      germY c ∈ IsLocalRing.maximalIdeal STK ↔ c ∈ y.asIdeal) := by sorry
