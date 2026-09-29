-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_snd_apply_eq_zero_of_apply_jOf_univ_eq_dualNumber_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.snd_apply_eq_zero_of_apply_jOf_univ_eq_dualNumber_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/a1ed8f27-7650-5cda-b8bc-c163394a550b
-- title:
--   Dual-number points with constant transcendental j are constant
-- statement:
--   Fix a prime $q$ and a nonzero $M'$ with $q \nmid M'$, and a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$ and $\ell_g \mid M'$. Let $A$ be a commutative ring in which $\ell_g$ and $M'$ are units, and assume the three equivariance riders: `hℓ`, that [`ModularCurve.IsGamma1Point`](def/ModularCurve_WeierstrassGamma1Pow.html#L10) at $\ell_g$ (a point $(x_P,y_P)$ on the affine Weierstrass equation with $(W.\mathrm{pre}\Psi\,\ell_g)(x_P)=0$ and $(x_Q,y_Q)=(x_P,y_P)$) is carried along variable changes; `hM`, that [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) is carried along variable changes via `kernelVariableChangeDeg`; and `hL`, that divisibility of `inLineMulPoly` is likewise carried along. Let $\mathcal G$ be a family of relative group laws on the projective Weierstrass models over $A$-algebras that is chord-tangent and has the origin as identity, and $\mathcal T$ a level transport at $q$ satisfying `IsSectionTransport`; assume moreover that variable changes and coefficient changes of projective models are realised by graded ring homomorphisms as in `hVC` and `hCO`. Let $P_0$ be a fine moduli package for the level moduli datum of `rigidDataH1Pow A ℓg M' q …`, whose points over an $A$-algebra $T$ are elliptic Weierstrass curves with unit discriminant equipped with a $\Gamma_0$-tuple of cyclic-kernel polynomials at the prime powers of $M'$, a $\Gamma_1$-point at $\ell_g$, and a Drinfeld basis of level $q$, subject to the `IsGamma1Link` divisibility, taken modulo variable change; thus $B_0$ is an $A$-algebra carrying a universal point `P₀.univ` classifying all such points uniquely. Let $\Omega$ be an algebraically closed field of characteristic zero which is an $A$-algebra with $q \neq 0$ in $\Omega$, and let $t \in \Omega$ be transcendental over $\mathbb{Q}$. Then for every $A$-algebra homomorphism $\varphi : B_0 \to \Omega[\varepsilon]$ into the dual numbers such that $\varphi$ sends the $j$-invariant of the universal point to the constant $t$, the $\varepsilon$-component of $\varphi(b)$ vanishes for every $b \in B_0$, i.e. $\varphi$ takes values in $\Omega$.
--
--   This is the formal unramifiedness of the $H_1$-level moduli ring $B_0$ over the $j$-line at a transcendental value of $j$: a tangent vector at such a point with constant $j$-invariant is zero, because a curve over $\Omega[\varepsilon]$ with constant $j \neq 0, 1728$ becomes constant after a variable change and the level data on a constant curve lift uniquely. It feeds the computation of reducedness and of the degree of $B_0$ over the function field of the $j$-line.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_snd_apply_eq_zero_of_apply_jOf_univ_eq_dualNumber_rigidDataH1Pow.lean

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

theorem ModularCurve.FullLevel.Diamond.snd_apply_eq_zero_of_apply_jOf_univ_eq_dualNumber_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : Type) [CommRing A]
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
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra A Ω] (hqΩ : ((q : ℕ) : Ω) ≠ 0)
    (t : Ω) (ht : Transcendental ℚ t) :
    ∀ φ : P₀.B₀ →ₐ[A] DualNumber Ω,
      φ ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf P₀.univ) = algebraMap Ω (DualNumber Ω) t →
        ∀ b : P₀.B₀, (φ b).snd = 0 := by sorry
