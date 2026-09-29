-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_ker_classify_mem_minimalPrimes_and_forall_exists_algEquiv_comap_eq_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.ker_classify_mem_minimalPrimes_and_forall_exists_algEquiv_comap_eq_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/31822d2a-5c0b-5c51-9bc9-ca4e8b55c2ea
-- title:
--   Every minimal prime is a j-fixing translate of the Tate kernel
-- statement:
--   Fix a prime $q$, an integer $M'\ne 0$ with $q\nmid M'$, and a prime $\ell_g$ with $\ell_g\equiv 11 \pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic $0$ containing a primitive $q\ell_g$-th root of unity $\xi$ for which some ring homomorphism $L\to\mathbb{C}$ sends $\xi$ to $\exp(2\pi i/(q\ell_g))$. Let $H_1\le(\mathbb{Z}/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb{Z}/q)^\times$ with the kernel of reduction to $(\mathbb{Z}/\ell_g)^\times$, and let $K\subseteq L((\mathsf q))$ be the intermediate field obtained by adjoining to $L$ the image, under coefficientwise extension along $\mathbb{Q}\to L$, of the $q$-expansion function field `xHFunctionField` of level $q^2M'$ and subgroup $H_1$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal, acting on $K$ compatibly, and let $j\in K$ be the element whose Laurent series is the coefficient extension of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), assumed nonzero; $\ell_g$ and $M'$ are units in $A$. Further data: the variable-change equivariance of the $\Gamma_1(\ell_g)$-point condition (affine equation, vanishing of $\mathrm{pre}\Psi_{\ell_g}$ at $x_P$, and $x_Q=x_P$, $y_Q=y_P$), of the $\Gamma_0(p^k)$ kernel-polynomial conditions, and of the divisibility by `inLineMulPoly`; a family $\mathcal{G}$ of relative group laws on projective Weierstrass models with invertible discriminant that is chord-tangent and has the origin as identity; a level transport $\mathcal{T}$ for Drinfeld $q$-bases satisfying the section-transport compatibilities; and the existence, for all $A$-algebras, of graded homomorphisms of the projective-model rings realising variable changes and coefficient maps and dominating the irrelevant ideal. Let $P_0$ be a fine moduli package, of finite type over $A$, for the level moduli datum `rigidDataH1Pow A ℓg M' q … 𝒢 𝒯` — whose points over an $A$-algebra $T$ are Weierstrass curves over $T$ with invertible discriminant equipped with $\Gamma_0$-kernel polynomials for the prime powers of $M'$, a $\Gamma_1(\ell_g)$-point, and a Drinfeld $q$-basis, subject to the $\Gamma_1$-link divisibility, taken up to variable change; so $P_0$ consists of an $A$-algebra $B_0$, a universal point, and unique classifying $A$-algebra maps. Finally let $x$ be a point of this problem over $K$ whose $j$-invariant has Laurent series [`ModularCurve.jqNModC L q`](def/ModularCurve_JqCoeff.html#L18). Then the kernel of the classifying homomorphism $B_0\to K$ attached to $x$ is a minimal prime of $B_0$, and every minimal prime $\mathfrak p$ of $B_0$ is the preimage of that kernel under some $A$-algebra automorphism $e$ of $B_0$ fixing the $j$-invariant of the universal point.
--
--   This is the component identification for the fine moduli ring of the level structure $\Gamma_0(M')\times\Gamma_1(\ell_g)\times$ Drinfeld $\Gamma(q)$: the Tate point over the $H_1$ $q$-expansion field cuts out an irreducible component, and all other components are obtained from it by $j$-fixing automorphisms of $B_0$. It is used to produce, for each minimal prime, an $A$-algebra map of the corresponding quotient into a Laurent series field, and thence in the reducedness statement for the residue-field fibre of the chart algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_ker_classify_mem_minimalPrimes_and_forall_exists_algEquiv_comap_eq_rigidDataH1Pow.lean

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
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.ker_classify_mem_minimalPrimes_and_forall_exists_algEquiv_comap_eq_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓg : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A P₀.B₀]
    (x : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L q) :
    RingHom.ker (P₀.classify x).toRingHom ∈ (⊥ : Ideal P₀.B₀).minimalPrimes ∧
    ∀ 𝔭 ∈ (⊥ : Ideal P₀.B₀).minimalPrimes,
      ∃ e : P₀.B₀ ≃ₐ[A] P₀.B₀,
        e ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf P₀.univ) =
          (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf P₀.univ ∧
        𝔭 = Ideal.comap ((e : P₀.B₀ →ₐ[A] P₀.B₀) : P₀.B₀ →+* P₀.B₀) (RingHom.ker (P₀.classify x).toRingHom) := by sorry
