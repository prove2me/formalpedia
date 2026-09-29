-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_weilPairing0_drinfeld_mapRing_eq_of_ker_classify_eq_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.weilPairing0_drinfeld_mapRing_eq_of_ker_classify_eq_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/93155c8e-eaa6-57a4-85c9-6982761069b3
-- title:
--   Equal `classify` kernels give equal Drinfeld Weil pairing values
-- statement:
--   Fix a commutative ring $A$, naturals $\ell g$ (prime), $M'$ (nonzero) and $q$ (prime) with $3 \le q$, together with three equivariance riders for the level data over arbitrary $A$-algebras $T$: `hℓ`, that the $\Gamma_1(\ell g)$-condition `IsGamma1Point` (the affine equation at $(x_P,y_P)$, vanishing of $(\,W.\mathrm{pre}\Psi_{\ell g})(x_P)$, and $x_Q = x_P$, $y_Q = y_P$) is carried by a variable change $C$ to `IsGamma1Point` for $C \bullet W$ and `D.variableChange C`; `hM`, that `IsGamma0PowAt W p k h` implies `IsGamma0PowAt (C • W) p k (kernelVariableChangeDeg C (gamma0PowDeg p k) h)`; and `hL`, that $h \mid$ `inLineMulPoly W ℓg n x` implies `kernelVariableChangeDeg C d h` divides `inLineMulPoly (C • W) ℓg n` at the transformed abscissa. Fix a family $\mathcal G$ of relative group laws on the projective Weierstrass models of elliptic curves over $A$-algebras which is chord–tangent and has the origin as identity, and a level transport $\mathcal T$ of Drinfeld pairs of level $q$ which is a section transport (its base-change and variable-change operations agree with the canonical maps of $\mathrm{Proj}$ on the two sections); assume further that every projective Weierstrass curve over an $A$-algebra admits graded homomorphisms of the model realising variable changes (`hVC`) and coefficient maps along $A$-algebra maps (`hCO`), each respecting the irrelevant ideals. Let $\mathcal R =$ `rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯` be the rigid Weierstrass data whose raw objects over $T$ consist of a Weierstrass curve with unit discriminant together with: a family of kernel polynomials $h_p$ satisfying `IsGamma0PowAt` at each prime power $p^{v_p(M')}$, a `LevelPData` which is a $\Gamma_1(\ell g)$-point, and a Drinfeld pair $(P,Q)$ of level $q$ for $\mathcal G$, subject to the link condition that if $\ell g \mid M'$ then $h_{\ell g}$ divides `inLineMulPoly W ℓg (ℓg ^ (M'.factorization ℓg - 1)) D.xP`; points over $T$ are raw objects modulo the variable-change relation. Let $P_0$ be a fine moduli package for the associated moduli datum: a commutative $A$-algebra $B_0$ with a universal point such that every point over every $A$-algebra factors uniquely through it, with `classify` the resulting classifying map. Let $K$ be a field over $A$, $\zeta \in A$ with $\zeta$ a primitive $q$-th root of unity in $K$, and $\Omega$ an algebraically closed field over $K$ and over $A$ compatibly. Let $x_1, x_2$ be points of the moduli datum over $K$ whose classifying maps $B_0 \to K$ have the same kernel, represented by raw data $y_1, y_2$ over $K$, and let $D_1, D_2$ be quadruples $(x_P,y_P,x_Q,y_Q)$ in $\Omega$ such that the two Drinfeld sections of the base change $z_i$ of $y_i$ to $\Omega$ pass through $(D_i.x_P, D_i.y_P)$ and $(D_i.x_Q, D_i.y_Q)$ respectively, in the sense of `IsSectionThrough`. Then, with each $z_i$.`curve` elliptic by unitness of its discriminant, the Weil pairing values `weilPairing0` $z_i$.`curve` $\Omega$ $q$ evaluated at the affine points with coordinates $D_i$ are equal as elements of $\Omega$.
--
--   This says that the Weil pairing of a Drinfeld basis of level $q$ is a function of the image point of the moduli problem: two $K$-points of the $H_1$-type moduli problem with the same kernel of the classifying map to $K$ have the same $q$-th root of unity as pairing value over an algebraically closed overfield. It is the input to the computation of the determinant of the diamond/relabelling action, [`ModularCurve.FullLevel.Diamond.det_eq_of_ker_classify_act_eq_of_relabel_drinfeld_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.det_eq_of_ker_classify_act_eq_of_relabel_drinfeld_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_weilPairing0_drinfeld_mapRing_eq_of_ker_classify_eq_rigidDataH1Pow.lean

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
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry WeierstrassProjModel
open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve.DrinfeldGlobal WeierstrassCurve.Affine

open scoped MatrixGroups

theorem ModularCurve.LevelModuliPackageAbs.weilPairing0_drinfeld_mapRing_eq_of_ker_classify_eq_rigidDataH1Pow
    (A : Type) [CommRing A] (ℓg M' q : ℕ) [Fact ℓg.Prime] [NeZero M'] [Fact q.Prime] (hq3 : 3 ≤ q)
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
    (K : Type) [Field K] [Algebra A K] (ζ : A) (hζ : IsPrimitiveRoot (algebraMap A K ζ) q)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A Ω] [Algebra K Ω] [IsScalarTower A K Ω]
    (x₁ x₂ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt K)
    (h : RingHom.ker (P₀.classify x₁).toRingHom = RingHom.ker (P₀.classify x₂).toRingHom)
    (y₁ y₂ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw K)
    (hy₁ : (Quot.mk _ y₁ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Pt K) = x₁)
    (hy₂ : (Quot.mk _ y₂ : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Pt K) = x₂)
    (D₁ D₂ : ModularCurve.LevelPData Ω)
    (hD₁ : IsSectionThrough ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₁).level.2.2.P D₁.xP D₁.yP ∧
      IsSectionThrough ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₁).level.2.2.Q D₁.xQ D₁.yQ)
    (hD₂ : IsSectionThrough ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₂).level.2.2.P D₂.xP D₂.yP ∧
      IsSectionThrough ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₂).level.2.2.Q D₂.xQ D₂.yQ) :
    letI z₁ := (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₁
    letI z₂ := (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₂
    letI _ : (z₁.curve).IsElliptic := ⟨z₁.isUnit_Δ⟩
    letI _ : (z₂.curve).IsElliptic := ⟨z₂.isUnit_Δ⟩
    ((weilPairing0 z₁.curve Ω (q : ℤ)
        (toPoint ((z₁.curve).baseChange Ω) D₁.xP D₁.yP)
        (toPoint ((z₁.curve).baseChange Ω) D₁.xQ D₁.yQ) : Ωˣ) : Ω) =
      ((weilPairing0 z₂.curve Ω (q : ℤ)
        (toPoint ((z₂.curve).baseChange Ω) D₂.xP D₂.yP)
        (toPoint ((z₂.curve).baseChange Ω) D₂.xQ D₂.yQ) : Ωˣ) : Ω) := by sorry
