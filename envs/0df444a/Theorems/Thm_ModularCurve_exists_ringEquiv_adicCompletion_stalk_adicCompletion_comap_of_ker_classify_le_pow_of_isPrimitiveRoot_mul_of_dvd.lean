-- Prove2me | Theorems.Thm_ModularCurve_exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_ker_classify_le_pow_of_isPrimitiveRoot_mul_of_dvd
-- name    : ModularCurve.exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_ker_classify_le_pow_of_isPrimitiveRoot_mul_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/cba11a0a-173e-5e48-aeca-0bd7bf2641a0
-- title:
--   Completed stalk of the two-chart model as 𝔭-adic completion
-- statement:
--   Let $q$ and $\ell$ be primes, $M'$ a nonzero natural number with $q \nmid M'$, $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$; let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, $\zeta \in L$ a primitive $q$-th root of unity, $\xi \in L$ a primitive $q\ell$-th root of unity with $\zeta = \xi^{\ell}$. Let $H_1 \le (\mathbb{Z}/q^2M')^{\times}$ be the intersection of the kernel of reduction to $(\mathbb{Z}/q)^{\times}$ with the kernel of reduction to $(\mathbb{Z}/\ell)^{\times}$, and let $K$ be the intermediate field of $L(\!(T)\!)$ generated over $L$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, $\zeta$ in the image of $A$, acting on $K$ compatibly with $L$, and let $\varpi$ generate the maximal ideal of $A$. Let $j \in K$ be nonzero with $q$-expansion the classical $j$-series, $X =$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) the pushout of the two charts $\operatorname{Spec}$ of the algebras of elements of $K$ integral over $A[j]$, respectively $A[j^{-1}]$, and let $z \in X$ be a point at which the germ of the image of $\varpi$ under the structure morphism to $\operatorname{Spec} A$ lies in the maximal ideal of the stalk. Let $y$ be a point of the finite chart $\operatorname{Spec} C$, $C =$ `chartAlgFin A K j`, with image $z$, and assume that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel the prime of $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), i.e. every elliptic Weierstrass curve over $\Omega$ with that $j$-invariant has no nonzero $q$-torsion affine point. Let $A_0$ be a commutative ring acting on $K$, $D$ a level moduli datum over $A_0$ (a functor $T \mapsto D.\mathrm{Pt}\,T$ on $A_0$-algebras with base change and a $j$-invariant function compatible with it), $P_0$ an abstract fine moduli package for $D$ with representing $A_0$-algebra $B_0$ and universal point, and $x$ a point of $D$ over $K$ whose $j$-invariant has $q$-expansion $j(\mathsf{q}^{q})$. Assume the classifying $A_0$-algebra map $B_0 \to K$ attached to $x$ has image exactly $C$, and that its kernel is contained in every power of the contraction $\mathfrak p$ of the prime of $y$ along the induced map $\theta : B_0 \to C$. Then $\mathfrak p$ is maximal, the image of $q$ in $B_0$ lies in $\mathfrak p$, and there is a ring isomorphism between the adic completion of the stalk of $X$ at $z$ along its maximal ideal and the $\mathfrak p$-adic completion of $B_0$, carrying the completed germ at $z$ of $\theta b$ to the image of $b$, for every $b \in B_0$.
--
--   This is the bridge between the geometric and the moduli-theoretic descriptions of a supersingular point in characteristic $q$: it identifies the completion of the local ring of the two-chart integral model of the $\Gamma_{H_1}(q^2M')$-curve with the completion of a representing algebra of an arbitrary level moduli problem at the corresponding maximal ideal, compatibly with the classifying map. It is used, in the auxiliary small-$q$ level frame, by the two results that produce such an isomorphism for the rigid Weierstrass level data $H_1$ and for its level automorphism variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_ker_classify_le_pow_of_isPrimitiveRoot_mul_of_dvd.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_ker_classify_le_pow_of_isPrimitiveRoot_mul_of_dvd
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

    (A₀ : Type) [CommRing A₀] [Algebra A₀ ↥K]
    (D : ModularCurve.LevelModuliDatum A₀) (P₀ : LevelModuliPackageAbs A₀ D)
    (x : D.Pt ↥K)
    (hxj : ((D.jOf x : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L q)
    (hmem : ∀ b : P₀.B₀, P₀.classify x b ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)
    (hsurj : ∀ c : ↥K, c ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j → ∃ b : P₀.B₀, P₀.classify x b = c)

    (hker : ∀ n : ℕ, RingHom.ker (P₀.classify x).toRingHom ≤
      (Ideal.comap ((P₀.classify x).toRingHom.codRestrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hmem)
        y.asIdeal) ^ n) :

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)
      let θ : P₀.B₀ →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :=
        (P₀.classify x).toRingHom.codRestrict (AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) hmem
      let 𝔭 : Ideal P₀.B₀ := Ideal.comap θ y.asIdeal
      𝔭.IsMaximal ∧ algebraMap A₀ P₀.B₀ (q : A₀) ∈ 𝔭 ∧
      ∃ β : CMP ≃+* AdicCompletion 𝔭 P₀.B₀,
        ∀ b : P₀.B₀, β (toC (germY (θ b))) = algebraMap P₀.B₀ (AdicCompletion 𝔭 P₀.B₀) b := by sorry
