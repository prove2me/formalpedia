-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_algHom_dualNumber_fst_eq_snd_ne_zero_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.exists_algHom_dualNumber_fst_eq_snd_ne_zero_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/22ad3a1f-606f-57e6-ab35-d625dd40e9e5
-- title:
--   Tangent vectors at geometric points of the H₁ moduli ring
-- statement:
--   Fix a prime $q$ and a positive integer $M'$ with $q \nmid M'$, and a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$ and $\ell_g \mid M'$. Let $A$ be a commutative ring in which the images of $\ell_g$ and of $M'$ are units. Three equivariance riders are assumed, for all $A$-algebras $T$, Weierstrass curves $W$ over $T$ and variable changes $C$: `hℓ`, that `IsGamma1Point W ℓg D` (the point $(x_P,y_P)$ lies on the affine equation, $(W.preΨ ℓg)(x_P)=0$, and $(x_Q,y_Q)=(x_P,y_P)$) is preserved by passing to $C \bullet W$ and `D.variableChange C`; `hM`, that `IsGamma0PowAt W p k h` (for $p^k = 2$ the two-kernel condition, otherwise the cyclic-generator-kernel conditions on $h$ relative to $W.preΨ$) is preserved under $h \mapsto$ `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; and `hL`, that divisibility of `inLineMulPoly W ℓg n x` by $h$ passes to the variable-changed polynomial and $((C.u^{-1})^2(x - C.r))$. Further, $\mathcal{G}$ is a family of relative group laws on the projective Weierstrass models of curves with unit discriminant over $A$-algebras, assumed chord–tangent (`IsChordTangent`: the group law is computed by a points-evaluation equivalence to the affine point group) and origin-normalised (`IsOriginIdentity`: its identity section is given by an origin-chart homomorphism killing $x/y$ and $z/y$); $\mathcal{T}$ is a transport of raw Drinfeld pairs along $A$-algebra maps and variable changes, compatible with the Drinfeld-basis level condition at $q$, and satisfying `IsSectionTransport`, which pins the transported sections to the actual pullbacks along the graded maps realising variable changes and coefficient maps. The hypotheses `hVC` and `hCO` assert that such realising graded homomorphisms of `projModelGradingCR`, with the required containment of irrelevant ideals, exist for every variable change and every $A$-algebra map. Finally $P_0$ is a fine moduli package for the moduli datum of `rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯`, whose points over $T$ are the variable-change classes of tuples consisting of a Weierstrass curve with unit discriminant, a family of kernel polynomials indexed by the prime factors of $M'$ with `IsGamma0PowAt` at the corresponding exponent, a $\Gamma_1$-point datum at $\ell_g$, a Drinfeld pair that is a basis at $q$, and the link condition that the kernel polynomial at $\ell_g$ divides `inLineMulPoly` of the $\Gamma_1$-point abscissa; thus $P_0$ consists of an $A$-algebra $B_0$ together with a point over $B_0$ through which every point over every $A$-algebra factors uniquely. Let $\Omega$ be an algebraically closed field of characteristic zero that is an $A$-algebra, with $q \neq 0$ in $\Omega$, and let $\varphi_0 : B_0 \to \Omega$ be an $A$-algebra homomorphism. The conclusion is that there is an $A$-algebra homomorphism $\varphi : B_0 \to \Omega[\varepsilon]/(\varepsilon^2)$ whose constant part agrees with $\varphi_0$ on every element, and for which the $\varepsilon$-part of $\varphi(b)$ is non-zero for at least one $b \in B_0$.
--
--   The statement says that the fine moduli ring $B_0$ of the $H_1$-type level structure (Drinfeld basis at $q$, cyclic kernels at the prime powers dividing $M'$, and a $\Gamma_1$-point at $\ell_g$) carries a non-trivial tangent vector at every $\Omega$-point, the first-order deformation being supplied by the moduli interpretation. It is used to show that no minimal prime of the relevant tensor product is maximal, which feeds the dimension-theoretic input to the study of the modular curve of full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_algHom_dualNumber_fst_eq_snd_ne_zero_rigidDataH1Pow.lean

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

theorem ModularCurve.FullLevel.Diamond.exists_algHom_dualNumber_fst_eq_snd_ne_zero_rigidDataH1Pow
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
    (φ₀ : P₀.B₀ →ₐ[A] Ω) :
    ∃ φ : P₀.B₀ →ₐ[A] DualNumber Ω,
      (∀ b : P₀.B₀, (φ b).fst = φ₀ b) ∧ ∃ b : P₀.B₀, (φ b).snd ≠ 0 := by sorry
