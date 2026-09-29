-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_algHom_laurentSeries_ker_eq_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow_of_isPrimitiveRoot
-- name    : ModularCurve.FullLevel.exists_algHom_laurentSeries_ker_eq_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/6022961d-b38f-5cd2-805f-a290d0d4ec0f
-- title:
--   Minimal primes of the full-level moduli ring are q-expansion kernels
-- statement:
--   Let $A$ be a discrete valuation domain, $q\ge 5$ and $\ell\ge 3$ primes with $\ell\neq q$, and $M'$ a nonzero natural number divisible by neither $q$ nor $\ell$; assume $q$ lies in the maximal ideal of $A$ while $\ell$ and $M'$ are invertible in $A$. Let $K'$ be a field of characteristic $0$ that is a fraction field of $A$, and let $r\in A$ be such that its image in $K'$ is a primitive $(q\ell)$-th root of unity admitting a ring embedding $K'\to\mathbb{C}$ carrying it to $\exp(2\pi i/(q\ell))$. Assume: level-$\ell$ data (two points satisfying the Weierstrass equation, both $x$-coordinates killed by $\mathrm{preΨ}_\ell$, with both independence elements units) are stable under variable change; the $\Gamma_0$-type kernel condition `IsGamma0PowAt` is stable under the variable change `kernelVariableChangeDeg`; $\mathcal G$ is a family of relative group laws on the Proj models of Weierstrass curves with unit discriminant over $A$-algebras, realising addition on affine points over fields and with identity section given by a chart homomorphism killing $x/y$ and $z/y$; $\mathcal T$ transports raw Drinfeld pairs along $A$-algebra maps and variable changes, preserving the Drinfeld $\Gamma(q)$-basis condition and compatible with the induced morphisms of Proj; and graded homomorphisms realising variable changes and coefficient maps on the Proj models exist, subject to the stated irrelevant-ideal conditions. Let $P_0$ be a fine moduli package for the combined datum `rigidDataPow A ℓ M' q`, with $B_0=P_0.B_0$ of finite type over $A$, and let $\mathfrak p$ be a minimal prime of $B_0$. Then there is an $A$-algebra homomorphism $\iota : B_0 \to K'(\!(\mathsf q)\!)$ with $\ker\iota=\mathfrak p$.
--
--   This is the geometric input of the $q$-expansion principle for the fine moduli ring carrying full Drinfeld $\Gamma(q)$-level together with $\Gamma(\ell)$- and $\Gamma_0(M')$-type data: every irreducible component of $\operatorname{Spec} B_0$ has a Tate point over the Laurent series field $K'(\!(\mathsf q)\!)$, exhibited as the kernel of a $q$-expansion map. It is used to prove that the relevant tensor products of quotients of $B_0$ are domains.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_algHom_laurentSeries_ker_eq_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow_of_isPrimitiveRoot.lean

import Mathlib
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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_algHom_laurentSeries_ker_eq_of_mem_minimalPrimes_levelModuliPackageAbs_gamma0Pow_of_isPrimitiveRoot
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (K' : Type) [Field K'] [CharZero K'] [Algebra A K'] [IsFractionRing A K']
    (r : A) (hr : IsPrimitiveRoot (algebraMap A K' r) (q * ℓ))
    (hιξ' : ∃ ι : K' →+* ℂ, ι (algebraMap A K' r) = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))

    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
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
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A P₀.B₀]
    (𝔭 : Ideal P₀.B₀) (h𝔭 : 𝔭 ∈ (⊥ : Ideal P₀.B₀).minimalPrimes) :
    ∃ ι : P₀.B₀ →ₐ[A] LaurentSeries K', RingHom.ker ι.toRingHom = 𝔭 := by sorry
