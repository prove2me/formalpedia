-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_isDomain_and_isIntegrallyClosed_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.isDomain_and_isIntegrallyClosed_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/ec3c7e17-942c-5d37-bddb-eb37d9f2e705
-- title:
--   Normality of generic fibres of the H₁ moduli components
-- statement:
--   Let $q$ be a prime and $M'$ a nonzero natural number with $q \nmid M'$, and let $\ell_g$ be a prime with $\ell_g \equiv 11 \pmod{12}$ dividing $M'$. Let $L$ be a field of characteristic zero carrying a primitive $(q\ell_g)$-th root of unity $\xi$ for which some ring embedding $L \to \mathbb{C}$ sends $\xi$ to $\exp(2\pi i/(q\ell_g))$. Let $H_1 \le (\mathbb{Z}/q^2M')^\times$ be the intersection of the kernels of reduction to $(\mathbb{Z}/q)^\times$ and to $(\mathbb{Z}/\ell_g)^\times$, and let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise image of the $q$-expansion function field of $X_{H_1}$ of level $q^2M'$. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal and with $\ell_g$ and $M'$ invertible in $A$; let $K$ be an $A$-algebra compatibly with $L$, and let $j \in K$ be an element, assumed nonzero, whose Laurent expansion is the coefficientwise image of the $q$-expansion of the modular $j$-invariant. Further data are: a family $\mathcal{G}$ of relative group laws on the graded projective models of Weierstrass curves with unit discriminant over $A$-algebras, which is chord–tangent and has identity supported at the origin chart; a transport $\mathcal{T}$ of pairs of sections along algebra maps and variable changes, preserving the Drinfeld-basis condition for $q$ and compatible with sections; and the equivariance hypotheses $h\ell$, $hM$, $hL$ (stability of $\Gamma_1(\ell_g)$-points, of the `IsGamma0PowAt` cyclic-kernel polynomials, and of the divisibility by `inLineMulPoly` under variable change) together with $hVC$, $hCO$ (existence, for every $A$-algebra, of graded ring maps realising a variable change, respectively a coefficient change, on the projective-model graded rings, with the irrelevant ideal condition). Let $P_0$ be a package representing the moduli datum `rigidDataH1Pow A ℓg M' q …`, that is, an $A$-algebra $B_0$ of finite type with a universal point such that, for every $A$-algebra $T$, each point over $T$ — a Weierstrass curve over $T$ with unit discriminant up to variable change, equipped with a polynomial at each prime $p \mid M'$ satisfying `IsGamma0PowAt` for $(p, v_p(M'))$, a $\Gamma_1(\ell_g)$-point, and a Drinfeld basis of the $q$-torsion, subject to the link condition that the polynomial at $\ell_g$ divides $\mathrm{inLineMulPoly}\,W\,\ell_g\,\ell_g^{v_{\ell_g}(M')-1}\,x_P$ — is the image of the universal point under a unique $A$-algebra homomorphism $B_0 \to T$. Then, for every minimal prime $\mathfrak{p}$ of $B_0$, the ring $L \otimes_A (B_0/\mathfrak{p})$ is a domain and is integrally closed.
--
--   This is the statement that the generic fibre of each irreducible component of the fine moduli ring of the $H_1$ level structure is a normal integral domain; it follows from flatness of $B_0$ over the discrete valuation ring $A$ together with smoothness of $L \otimes_A B_0$ over $L$ and the normality of the components of a smooth algebra. It feeds the corresponding integrally closed statement for the quotients by minimal primes, used in the analysis of the function field of the modular curve at full level $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_isDomain_and_isIntegrallyClosed_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_rigidDataH1Pow.lean

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

theorem ModularCurve.FullLevel.Diamond.isDomain_and_isIntegrallyClosed_tensorProduct_quotient_of_mem_minimalPrimes_levelModuliPackageAbs_rigidDataH1Pow
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
    (𝔭 : Ideal P₀.B₀) (h𝔭 : 𝔭 ∈ (⊥ : Ideal P₀.B₀).minimalPrimes) :
    IsDomain (TensorProduct A L (P₀.B₀ ⧸ 𝔭)) ∧ IsIntegrallyClosed (TensorProduct A L (P₀.B₀ ⧸ 𝔭)) := by sorry
