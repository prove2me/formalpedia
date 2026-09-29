-- Prove2me | Theorems.Thm_ModularCurve_exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_ker_classify_le_pow
-- name    : ModularCurve.exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_ker_classify_le_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/7be937fe-8e41-549c-9aa8-7dc9e5e58770
-- title:
--   Completed stalk of two-chart model versus 𝔭-adic moduli completion
-- statement:
--   Fix a prime $q \ge 5$, a nonzero natural number $M'$ with $q \nmid M'$, and a prime $\ell \ge 3$ with $\ell \ne q$ and $\ell \nmid M'$. Let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of level $q\ell$, with $\zeta \in L$ a primitive $q$-th root of unity and $\xi \in L$ a primitive $q\ell$-th root of unity, and let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise image of the $q$-expansion function field of $X_H$ of level $(q\ell)^2M'$, where $H \le (\mathbb{Z}/(q\ell)^2M')^\times$ is the kernel of reduction to $(\mathbb{Z}/q\ell)^\times$, i.e. the units congruent to $1$ modulo $q\ell$. Let $A$ be a discrete valuation ring with fraction field $L$ such that $q$ lies in its maximal ideal and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly with $L$, and let $j \in K$ be nonzero with Laurent image the coefficient embedding of the $q$-expansion $q^{-1}\cdot(\text{integral }j\text{-numerator})$; let $\varpi$ generate the maximal ideal of $A$. Write $X$ for the two-chart integral model over $A$, the pushout of $\operatorname{Spec}$ of the inclusions of the subalgebras of elements of $K$ integral over $A[j]$, respectively over $A[j^{-1}]$, into the corresponding middle algebra. Let $z \in X$ be a point at which the germ of the global section coming from $\varpi$ via the structure morphism to $\operatorname{Spec} A$ lies in the maximal ideal of the stalk, let $y$ be a point of $\operatorname{Spec} C$, $C$ the algebra of elements of $K$ integral over $A[j]$, with $\iota_{\mathrm{fin}}(y) = z$, and assume that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi : C \to \Omega$ with kernel the prime of $y$, the value $\varphi(j)$ lies in $\mathrm{ssJSet}\,q\,\Omega$, the set of $u \in \Omega$ such that every elliptic Weierstrass curve over $\Omega$ with $j$-invariant $u$ has no nonzero affine point killed by $q$. Let further $A_0$ be a commutative ring with $K$ an $A_0$-algebra, $D$ a level moduli datum over $A_0$ (a functor $T \mapsto D.\mathrm{Pt}\,T$ on $A_0$-algebras with functorial base change and a $j$-invariant function commuting with it), and $P_0$ an abstract fine moduli package for $D$: an $A_0$-algebra $B_0$ with a universal point in $D.\mathrm{Pt}\,B_0$ through which every $D$-point of every $A_0$-algebra factors uniquely. Let $x$ be a $K$-point of $D$ whose $j$-invariant has Laurent image the $q\ell$-fold $q$-expansion of $j$, assume the classifying homomorphism of $x$ takes values exactly in $C$ (every value lies in $C$, and every element of $C$ is a value), write $\theta : B_0 \to C$ for the induced map and $\mathfrak p = \theta^{-1}(y)$, and assume $\ker \theta \subseteq \mathfrak p^n$ for all $n$. Then $\mathfrak p$ is maximal, the image of $q$ in $B_0$ lies in $\mathfrak p$, and there is a ring isomorphism $\beta$ from the completion of the stalk of $X$ at $z$ with respect to its maximal ideal onto the $\mathfrak p$-adic completion of $B_0$ such that for every $b \in B_0$ the image in the completed stalk of the germ at $z$ of $\theta b$ is carried by $\beta$ to the image of $b$ in the $\mathfrak p$-adic completion of $B_0$.
--
--   This is the bridge identifying the completed local ring of the integral two-chart model of the modular curve at a supersingular point of the fibre over $q$ with the $\mathfrak p$-adic completion of a ring representing an abstract level moduli problem, compatibly with the classifying map. It is used by the two results of the full-level auxiliary development that produce such a moduli package together with the resulting isomorphism of completions, with and without the level automorphism bookkeeping.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_ker_classify_le_pow.lean

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

theorem ModularCurve.exists_ringEquiv_adicCompletion_stalk_adicCompletion_comap_of_ker_classify_le_pow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
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
    (hxj : ((D.jOf x : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L (q * ℓ))
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
