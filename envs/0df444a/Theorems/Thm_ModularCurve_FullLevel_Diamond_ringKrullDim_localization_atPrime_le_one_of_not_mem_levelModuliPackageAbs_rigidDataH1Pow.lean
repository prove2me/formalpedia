-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_ringKrullDim_localization_atPrime_le_one_of_not_mem_levelModuliPackageAbs_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.ringKrullDim_localization_atPrime_le_one_of_not_mem_levelModuliPackageAbs_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/8db38850-3c8e-5898-ad7a-ded9ce2f3ae1
-- title:
--   Dimension ≤ 1 at q-invertible maximal ideals of B₀
-- statement:
--   Let $q$ be a prime, let $\ell_g$ be a prime with $\ell_g \equiv 11 \pmod{12}$, and let $M'$ be a nonzero natural number with $q \nmid M'$ and $\ell_g \mid M'$. Let $A_0$ be a discrete valuation domain whose maximal ideal is $(q)$ and whose residue field is finite, and assume $\ell_g$ and $M'$ are invertible in $A_0$. Assume three equivariance hypotheses for variable changes over $A_0$-algebras: the $\Gamma_1(\ell_g)$-point condition is preserved, the condition `IsGamma0PowAt` (for $p^k = 2$ the `IsTwoKernel` condition, otherwise: degree at most $\varphi(p^k)/2$, leading coefficient in that degree $1$, $h\cdot\mathrm{pre}\Psi_{p^{k-1}} \mid \mathrm{pre}\Psi_{p^k}$, and $h$ divides the relevant `smulNumerator`s) is preserved by `kernelVariableChangeDeg`, and divisibility of `inLineMulPoly` is preserved. Assume given group laws $\mathcal G$ on the graded projective models over all $A_0$-algebras that are chord–tangent (their points on fields are additive and Galois-equivariant) and have the origin as identity, a level transport $\mathcal T$ for Drinfeld $q$-bases that is a section transport, and hypotheses hVC, hCO providing graded ring homomorphisms of the projective-model coordinate rings which realise variable changes, respectively coefficient maps, and pull back the irrelevant ideal suitably. These data define the rigid Weierstrass datum `rigidDataH1Pow`: over an $A_0$-algebra $T$, a Weierstrass curve $W$ with unit discriminant together with a family $(h_p)$ indexed by the prime factors of $M'$ satisfying `IsGamma0PowAt` at $p^{v_p(M')}$, a quadruple $(x_P,y_P,x_Q,y_Q)$ with $(x_P,y_P)$ on the affine curve, $\mathrm{pre}\Psi_{\ell_g}(x_P)=0$ and $(x_Q,y_Q)=(x_P,y_P)$, and a pair of sections forming a Drinfeld $q$-basis for $\mathcal G$, subject to the link condition that $h_{\ell_g}$ divides $\mathrm{inLineMulPoly}\,W\,\ell_g\,\ell_g^{v_{\ell_g}(M')-1}\,x_P$, all taken modulo variable changes and with $j$-invariant as the $j$-function. Let $P_0$ be an abstract fine moduli package for this datum: an $A_0$-algebra $B_0$ with a universal point such that every point over an $A_0$-algebra $T$ is the image of the universal one under a unique $A_0$-algebra map $B_0 \to T$; assume $B_0$ is of finite type over $A_0$. Then for every maximal ideal $\mathfrak m$ of $B_0$ with $\mathrm{algebraMap}\,A_0\,B_0\,(q) \notin \mathfrak m$, the Krull dimension of the localisation of $B_0$ at $\mathfrak m$ is at most $1$.
--
--   This is the one-dimensionality of the fine moduli ring of the combined level structure ($\Gamma_0(M') \cap \Gamma_1(\ell_g)$ with link, together with a Drinfeld $q$-basis) at points of the fibre where $q$ is invertible, in the style of the regularity and dimension statements for moduli of elliptic curves with level structure. It feeds the statement that the adic completion of $B_0$ at such a maximal ideal is a domain and integrally closed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_ringKrullDim_localization_atPrime_le_one_of_not_mem_levelModuliPackageAbs_rigidDataH1Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.FullLevel.Diamond.ringKrullDim_localization_atPrime_le_one_of_not_mem_levelModuliPackageAbs_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (ℓg M' : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) [NeZero M'] (hM'q : ¬ q ∣ M') (hℓgM' : ℓg ∣ M')

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : maximalIdeal A₀ = Ideal.span {(q : A₀)}) [Finite (ResidueField A₀)]

    (hℓA : IsUnit ((ℓg : ℕ) : A₀)) (hM'A : IsUnit ((M' : ℕ) : A₀))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

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
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A₀ P₀.B₀]
    (𝔪 : Ideal P₀.B₀) [𝔪.IsMaximal] (hq𝔪 : algebraMap A₀ P₀.B₀ (q : A₀) ∉ 𝔪) :
    ringKrullDim (Localization.AtPrime 𝔪) ≤ 1 := by sorry
