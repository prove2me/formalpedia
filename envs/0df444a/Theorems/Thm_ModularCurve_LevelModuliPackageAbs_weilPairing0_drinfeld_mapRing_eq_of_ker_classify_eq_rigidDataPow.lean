-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_weilPairing0_drinfeld_mapRing_eq_of_ker_classify_eq_rigidDataPow
-- name    : ModularCurve.LevelModuliPackageAbs.weilPairing0_drinfeld_mapRing_eq_of_ker_classify_eq_rigidDataPow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/17d77de5-f202-5b6a-98a8-b219906a9401
-- title:
--   Equal classifying kernels give equal q-Weil pairing values
-- statement:
--   Fix a commutative ring $A$, a prime $\ell$, a nonzero natural number $M'$ and a prime $q$ with $3 \le q$. Assume: $\mathtt{h\ell}$, that over every $A$-algebra $T$ a Katz level-$\ell$ datum $D$ (a quadruple $(x_P,y_P,x_Q,y_Q)$ satisfying the affine equation, with $\mathrm{pre}\Psi_\ell$ vanishing at $x_P$ and $x_Q$ and both independence elements units) transforms under a variable change $C$ into such a datum for $C \cdot W$; $\mathtt{hM}$, the analogous stability of the predicate `IsGamma0PowAt` under `kernelVariableChangeDeg`. Let $\mathcal{G}$ be a family of relative group laws on the graded projective models of Weierstrass curves with unit discriminant over $A$-algebras, assumed chord–tangent (a points-evaluation equivalence additive and Galois-equivariant exists) and with identity section sitting at the origin chart with $x/y = z/y = 0$; let $\mathcal{T}$ be a transport of raw Drinfeld pairs along $A$-algebra maps and variable changes, assumed to be induced by the corresponding maps of projective models (`IsSectionTransport`). Assume further that every variable change and every coefficient change of a projective Weierstrass model is realised by a graded ring homomorphism satisfying the stated irrelevant-ideal condition. Let $P_0$ be a fine moduli package for the moduli datum of `rigidDataPow A ℓ M' q …`, whose raw objects over $T$ consist of a Weierstrass curve with unit discriminant together with kernel polynomials at the prime powers dividing $M'$, a Katz level-$\ell$ datum, and a raw Drinfeld pair forming a Drinfeld basis of the $q$-torsion. Let $K$ be a field over $A$, $\zeta \in A$ with image a primitive $q$-th root of unity in $K$, and $\Omega$ an algebraically closed field over $K$ compatible with $A$. Let $x_1, x_2$ be $K$-points of this moduli problem whose classifying $A$-algebra homomorphisms out of $P_0.B_0$ have the same kernel, let $y_1, y_2$ be raw representatives of $x_1, x_2$, and set $z_i$ to be the base change of $y_i$ along $K \to \Omega$. Let $D_1, D_2$ be quadruples of elements of $\Omega$ giving affine coordinates (in the sense of `IsSectionThrough`) for the two sections $P$ and $Q$ of the Drinfeld pair slot of $z_1$, respectively $z_2$. Then, with the curves of $z_1$ and $z_2$ elliptic by virtue of their unit discriminants, the $q$-Weil pairing value `weilPairing0` of the points of the base change of $z_1$'s curve with coordinates $(D_1.x_P, D_1.y_P)$ and $(D_1.x_Q, D_1.y_Q)$ equals that of the corresponding two points attached to $z_2$ and $D_2$, as elements of $\Omega$.
--
--   This is the statement that the $q$-Weil pairing of a Drinfeld basis, computed through affine coordinates of the two sections after base change to an algebraically closed field, depends only on the kernel of the classifying homomorphism of the moduli point, i.e. only on the point of the coarse quotient; it is the $\Gamma(q)$-slot counterpart of the corresponding invariance for Katz level structures. It feeds the comparison of determinants of relabelling matrices for full level structures, [`ModularCurve.FullLevel.det_eq_of_ker_classify_act_eq_of_relabel_gamma0Pow`](thm.html#ModularCurve.FullLevel.det_eq_of_ker_classify_act_eq_of_relabel_gamma0Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_weilPairing0_drinfeld_mapRing_eq_of_ker_classify_eq_rigidDataPow.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry WeierstrassProjModel
open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve.DrinfeldGlobal WeierstrassCurve.Affine

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.weilPairing0_drinfeld_mapRing_eq_of_ker_classify_eq_rigidDataPow
    (A : Type) [CommRing A] (ℓ M' q : ℕ) [Fact ℓ.Prime] [NeZero M'] [Fact q.Prime] (hq3 : 3 ≤ q)
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
    (K : Type) [Field K] [Algebra A K] (ζ : A) (hζ : IsPrimitiveRoot (algebraMap A K ζ) q)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] [Algebra A Ω] [Algebra K Ω] [IsScalarTower A K Ω]
    (x₁ x₂ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt K)
    (h : RingHom.ker (P₀.classify x₁).toRingHom = RingHom.ker (P₀.classify x₂).toRingHom)
    (y₁ y₂ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw K)
    (hy₁ : (Quot.mk _ y₁ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Pt K) = x₁)
    (hy₂ : (Quot.mk _ y₂ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Pt K) = x₂)
    (D₁ D₂ : ModularCurve.LevelPData Ω)
    (hD₁ : IsSectionThrough ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₁).level.2.2.P D₁.xP D₁.yP ∧
      IsSectionThrough ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₁).level.2.2.Q D₁.xQ D₁.yQ)
    (hD₂ : IsSectionThrough ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₂).level.2.2.P D₂.xP D₂.yP ∧
      IsSectionThrough ((rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₂).level.2.2.Q D₂.xQ D₂.yQ) :
    letI z₁ := (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₁
    letI z₂ := (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing (IsScalarTower.toAlgHom A K Ω) y₂
    letI _ : (z₁.curve).IsElliptic := ⟨z₁.isUnit_Δ⟩
    letI _ : (z₂.curve).IsElliptic := ⟨z₂.isUnit_Δ⟩
    ((weilPairing0 z₁.curve Ω (q : ℤ)
        (toPoint ((z₁.curve).baseChange Ω) D₁.xP D₁.yP)
        (toPoint ((z₁.curve).baseChange Ω) D₁.xQ D₁.yQ) : Ωˣ) : Ω) =
      ((weilPairing0 z₂.curve Ω (q : ℤ)
        (toPoint ((z₂.curve).baseChange Ω) D₂.xP D₂.yP)
        (toPoint ((z₂.curve).baseChange Ω) D₂.xQ D₂.yQ) : Ωˣ) : Ω) := by sorry
