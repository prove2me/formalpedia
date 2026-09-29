-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_smooth_tensorProduct_levelModuliPackageAbs_rigidDataH1Pow_of_isFractionRing
-- name    : ModularCurve.FullLevel.Diamond.smooth_tensorProduct_levelModuliPackageAbs_rigidDataH1Pow_of_isFractionRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/9772bbb6-909b-5fdb-8c4d-2c3893c86df4
-- title:
--   Smoothness of the generic fibre of the H₁ moduli ring
-- statement:
--   Let $A$ be a discrete valuation domain, $q$ a prime, $M'$ a nonzero natural number with $q \nmid M'$, and $\ell_g$ a prime with $\ell_g \equiv 11 \pmod{12}$ and $\ell_g \mid M'$; assume $q$ lies in the maximal ideal of $A$ while $\ell_g$ and $M'$ are units in $A$. Assume the three variable-change compatibilities $h\ell$, $hM$, $hL$: $\Gamma_1$-points (an affine point $(x_P,y_P)$ with $(W.\mathrm{pre}\Psi_{\ell_g})(x_P)=0$ and $(x_Q,y_Q)=(x_P,y_P)$), the predicates `IsGamma0PowAt` for cyclic generators of $p^k$-kernels, and divisibility of `inLineMulPoly` are each preserved by `kernelVariableChangeDeg`-twisting along a Weierstrass variable change. Let $\mathcal{G}$ be a family of relative group laws on the projective models of discriminant-unit curves over $A$-algebras that is chord-tangent and has the origin as identity, and $\mathcal{T}$ a transport of Drinfeld pairs for $\mathcal{G}$ at $q$ satisfying `IsSectionTransport`; assume further that variable changes and coefficient maps of projective models are realised by graded ring homomorphisms (hypotheses `hVC`, `hCO`). Let $P_0$ be a fine moduli package for the moduli datum of the rigid data `rigidDataH1Pow` — curves with invertible discriminant equipped with a $\Gamma_0$-power structure at each prime factor of $M'$, a $\Gamma_1$-point of order $\ell_g$, and a Drinfeld $q$-basis, subject to the link condition `IsGamma1Link`, taken modulo variable change — so $B_0$ is an $A$-algebra with a universal point representing the functor, and assume $B_0$ is of finite type over $A$. Then for any fraction field $K$ of $A$ with $q \neq 0$ in $K$, the $K$-algebra $K \otimes_A B_0$ is smooth, i.e. formally smooth and of finite presentation.
--
--   This is the smoothness of the generic fibre of the fine moduli ring of the $H_1$-type level structure (full $q$-level together with $\Gamma_0(M')$-power and $\Gamma_1(\ell_g)$ data) over a discrete valuation ring in which $q$ is a unit generically. It feeds the regularity and normality analysis of the moduli ring: the deduction that the fibres over minimal primes are integrally closed domains, that minimal primes of the base change are not maximal, and the reducedness statement for the associated package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_smooth_tensorProduct_levelModuliPackageAbs_rigidDataH1Pow_of_isFractionRing.lean

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
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.smooth_tensorProduct_levelModuliPackageAbs_rigidDataH1Pow_of_isFractionRing
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)

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
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]
    (hqK : (q : K) ≠ 0) :
    Algebra.Smooth K (TensorProduct A K P₀.B₀) := by sorry
