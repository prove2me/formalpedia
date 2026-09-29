-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_levelModuliPackageAbs_gamma0Pow_ringEquiv_adicCompletion_stalk_const_of_mem_ssJSet
-- name    : ModularCurve.FullLevel.AuxLevel.exists_levelModuliPackageAbs_gamma0Pow_ringEquiv_adicCompletion_stalk_const_of_mem_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/41ba34a8-4cc4-5c06-b4d0-d4566b6ea9f0
-- title:
--   Moduli reading of a supersingular point of the integral model
-- statement:
--   Let $q\ge 5$ and $\ell\ge 3$ be distinct primes, $M'$ a nonzero natural number divisible by neither $q$ nor $\ell$; let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $q\ell$, with $\zeta\in L$ a primitive $q$-th and $\xi\in L$ a primitive $q\ell$-th root of unity. Let $K$ be the intermediate field of $L \subseteq$ `LaurentSeries L` obtained as [`ModularCurve.laurentBaseChange L`](def/ModularCurve_LaurentCoeff.html#L103) of the function field [`ModularCurve.xHFunctionField ((q*ℓ)^2 * M') (ModularCurve.FullLevel.levelH (q*ℓ) M')`](def/ModularCurve_XH.html#L79), the subgroup `levelH` being the kernel of the reduction $(\mathbb{Z}/(q\ell)^2M')^\times \to (\mathbb{Z}/(q\ell))^\times$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $q$ lies in the maximal ideal and $\zeta$ is in the image of $A$, equipped with an $A$-algebra structure on $K$ compatible with $L$, let $\varpi$ generate the maximal ideal of $A$, and let $j \in K$ be nonzero with image in `LaurentSeries L` the coefficientwise embedding of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Let $\mathcal X$ be the two-chart integral model [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the pushout of the two affine charts $\operatorname{Spec}$ of the algebras of elements of $K$ integral over $A[j]$ and over $A[j^{-1}]$. Let $z$ be a point of $\mathcal X$ at which the germ $\varpi z$ of $\varpi$, pulled back along the structure morphism to $\operatorname{Spec} A$, lies in the maximal ideal of the stalk, and let $y$ be a point of the finite chart $\operatorname{Spec}$ of `chartAlgFin` with image $z$; assume $y$ is supersingular in the sense that for every algebraically closed field $\Omega$ of characteristic $q$ and every ring homomorphism $\varphi$ from `chartAlgFin` to $\Omega$ with kernel the prime of $y$, the value $\varphi(j)$ lies in [`ModularCurve.ssJSet q Ω`](def/ModularCurve_SupersingularModuli.html#L7), that is, every elliptic curve over $\Omega$ with that $j$-invariant has no nonzero affine point killed by $q$. Then there exist: a discrete valuation domain $A_0$ with maximal ideal $(q)$ and finite residue field, making $A$ a module-finite extension of $A_0$ with injective structure map, together with $\zeta_A \in A$ lifting $\zeta$ and generating $A$ as an $A_0$-algebra, with $\ell$ and $M'$ units in $A_0$; the two stability statements $h\ell$ and $hM$ (level-$\ell$ Katz data and $\Gamma_0(p^k)$ kernel polynomials are carried along variable changes, the latter via `kernelVariableChangeDeg`); group laws $\mathcal G$ over $A_0$ that are chord-tangent and origin-identity, a level transport $\mathcal T$ for $q$ that is a section transport, and the pinning data $hVC$, $hCO$ supplying graded homomorphisms of the projective-model gradings realising variable changes and coefficient maps, subject to the irrelevant-ideal condition; a package `LevelModuliPackageAbs` $P_0$ over $A_0$ finely representing the moduli datum of `rigidDataPow A₀ ℓ M' q`, with $P_0.B_0$ of finite type over $A_0$; a maximal ideal $\mathfrak p$ of $P_0.B_0$ containing the image of $q$ at which the universal $j$-invariant `P₀.j₀` is supersingular in the same sense; a ring isomorphism $\beta$ from the adic completion of the stalk $\mathcal O_{\mathcal X,z}$ at its maximal ideal to the $\mathfrak p$-adic completion of $P_0.B_0$; a ring homomorphism $\sigma_0 : A \to \widehat{(P_0.B_0)}_{\mathfrak p}$ restricting on $A_0$ to $A_0 \to P_0.B_0 \to \widehat{(P_0.B_0)}_{\mathfrak p}$; and witnesses that [`ModularCurve.jqNModC L (q*ℓ)`](def/ModularCurve_JqCoeff.html#L18) belongs to $K$ and to the finite chart algebra, such that $\beta$ carries the completed germ of each $a \in A$ to $\sigma_0(a)$, and carries the completed germ at $z$ of `jqNModC L (q*ℓ)`, read through the finite chart, to the image of `P₀.j₀` in $\widehat{(P_0.B_0)}_{\mathfrak p}$.
--
--   This is the curve-side bookkeeping for the identification of the completed local ring of the integral model of the full-level cyclotomic modular curve at a supersingular point of the fibre at $q$ with the completed local ring of a fine moduli scheme for Weierstrass curves with $\Gamma_0(M')$, level-$\ell$ and Drinfeld level-$q$ data, carried out over the unramified sub-base $A_0$ rather than over $A$. It is used in the construction of the Drinfeld-basis adic description of that completed stalk together with its Hasse parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_levelModuliPackageAbs_gamma0Pow_ringEquiv_adicCompletion_stalk_const_of_mem_ssJSet.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.FullLevel.AuxLevel.exists_levelModuliPackageAbs_gamma0Pow_ringEquiv_adicCompletion_stalk_const_of_mem_ssJSet
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
        φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet q Ω) :
    ∃ (A₀ : Type) (_ : CommRing A₀) (_ : IsDomain A₀) (_ : IsDiscreteValuationRing A₀)
      (_ : IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)}) (_ : Finite (IsLocalRing.ResidueField A₀))

      (_ : Algebra A₀ A) (_ : Function.Injective (algebraMap A₀ A)) (_ : Module.Finite A₀ A)
      (ζA : A) (_ : algebraMap A L ζA = ζ) (_ : Algebra.adjoin A₀ {ζA} = ⊤)
      (_ : IsUnit ((ℓ : ℕ) : A₀)) (_ : IsUnit ((M' : ℕ) : A₀))

      (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
        (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
          ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
      (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
        (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
          ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
      (𝒢 : GroupLaws A₀) (_ : 𝒢.IsChordTangent) (_ : 𝒢.IsOriginIdentity)
      (𝒯 : LevelTransport A₀ 𝒢 q) (_ : 𝒯.IsSectionTransport)
      (hVC : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
        ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
          (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
          IsVariableChangeHom W C φ)
      (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
        (W : WeierstrassCurve.Projective T),
        ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
          (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
            (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
          IsCoefficientHom W f.toRingHom φ)

      (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
      (_ : Algebra.FiniteType A₀ P₀.B₀)

      (𝔭 : Ideal P₀.B₀) (_ : 𝔭.IsMaximal) (_ : algebraMap A₀ P₀.B₀ (q : A₀) ∈ 𝔭)
      (_ : ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω] (φ : P₀.B₀ →+* Ω),
        RingHom.ker φ = 𝔭 → φ P₀.j₀ ∈ ModularCurve.ssJSet q Ω)
      (β : AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≃+* AdicCompletion 𝔭 P₀.B₀)

      (σ₀ : A →+* AdicCompletion 𝔭 P₀.B₀)
      (_ : ∀ a₀ : A₀, σ₀ (algebraMap A₀ A a₀) =
        algebraMap P₀.B₀ (AdicCompletion 𝔭 P₀.B₀) (algebraMap A₀ P₀.B₀ a₀))
      (hjK : ModularCurve.jqNModC L (q * ℓ) ∈ K)
      (hjC : (⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K) ∈ AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j),

      let STK := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
      let CMP := (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
      let toC : STK →+* CMP := algebraMap STK CMP
      let germY : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* STK :=
        ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ
            ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j) ''ᵁ ⊤) z ⟨y, trivial, hy⟩).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).appIso ⊤).inv.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))).inv.hom)

      (∀ a : A, β (algebraMap ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
            (AdicCompletion (IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
          (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
            (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)))) =
        σ₀ a) ∧

      β (toC (germY (⟨(⟨ModularCurve.jqNModC L (q * ℓ), hjK⟩ : ↥K), hjC⟩ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)))) =
        algebraMap P₀.B₀ (AdicCompletion 𝔭 P₀.B₀) P₀.j₀ := by sorry
