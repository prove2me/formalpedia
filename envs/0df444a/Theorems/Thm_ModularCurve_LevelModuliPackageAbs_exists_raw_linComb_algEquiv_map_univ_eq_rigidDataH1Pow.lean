-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_raw_linComb_algEquiv_map_univ_eq_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_raw_linComb_algEquiv_map_univ_eq_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/fc5e47a5-a87f-59fa-b08a-7da25a538bda
-- title:
--   Basis relabelling by γ is induced by an automorphism of B₀
-- statement:
--   Fix a prime $q$, naturals $\ell_g$ and $M'$ with $M'\neq 0$, and a commutative ring $A_0$. Assume: $h_\ell$, $h_M$, $h_L$, stating that over every $A_0$-algebra $T$ a variable change $C$ carries a $\Gamma_1$-datum (a `LevelPData` whose point lies on the curve, is killed by $\operatorname{pre}\Psi_{\ell_g}$, and whose two points coincide) to the transformed datum, carries a polynomial satisfying `IsGamma0PowAt` for $p^k$ to its `kernelVariableChangeDeg`-transform, and preserves divisibility of `inLineMulPoly`; group laws $\mathcal G$ on projective Weierstrass models with unit discriminant that are chord-and-tangent and have the origin as identity; a level transport $\mathcal T$ of raw Drinfeld pairs for $q$ satisfying `IsSectionTransport`; and $h_{VC}$, $h_{CO}$, providing graded ring maps of the homogeneous coordinate rings realising variable changes and coefficient changes. Let $P_0$ be a fine moduli package for the level moduli datum of `rigidDataH1Pow`: an $A_0$-algebra $B_0$ with a point `univ` such that every point over any $A_0$-algebra is its image under a unique $A_0$-algebra map. Let $x$ be a raw datum over $B_0$ (curve with unit discriminant, $\Gamma_0(M')$-component, $\Gamma_1$-datum, Drinfeld pair, with the linkage condition) whose class is `univ`, let $h_\Delta$ witness that the discriminant of the pair's curve is a unit, and let $a,b,c,d$ be naturals with $ad-bc$ a unit in $\mathbb{Z}/q$. Then there are a raw datum $y$ over $B_0$ and an $A_0$-algebra automorphism $\sigma$ of $B_0$ such that $y$ has the same curve, the same $\Gamma_0$- and $\Gamma_1$-components as $x$, its Drinfeld pair has the same curve with sections $aP+bQ$ and $cP+dQ$ formed by `linComb` from the sections of $x$, and $\sigma$ sends `univ` to the class of $y$.
--
--   This is the package-level form of the action of $\mathrm{GL}_2(\mathbb{Z}/q)$ on Drinfeld bases: relabelling the basis of the universal object of a fine moduli problem is induced by an automorphism of the representing algebra $B_0$. It is used in the study of the rings representing the $H_1$-type moduli problem, in particular in the construction of automorphisms of $B_0$ adapted to power-series expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_raw_linComb_algEquiv_map_univ_eq_rigidDataH1Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_raw_linComb_algEquiv_map_univ_eq_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (ℓg M' : ℕ) [NeZero M']
    (A₀ : Type) [CommRing A₀]
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
    (x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)
    (hΔ : IsUnit x.level.2.2.curve.Δ)

    (a b c d : ℕ) (hγ : IsUnit (((a * d : ℤ) - (b * c : ℤ) : ℤ) : ZMod q)) :
    ∃ (y : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw P₀.B₀) (σ : P₀.B₀ ≃ₐ[A₀] P₀.B₀),
      y.curve = x.curve ∧ y.level.1 = x.level.1 ∧ y.level.2.1 = x.level.2.1 ∧
      y.level.2.2 =
        { curve := x.level.2.2.curve
          P := linComb (𝒢 P₀.B₀ x.level.2.2.curve hΔ) x.level.2.2.P x.level.2.2.Q a b
          Q := linComb (𝒢 P₀.B₀ x.level.2.2.curve hΔ) x.level.2.2.P x.level.2.2.Q c d } ∧
      (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map (σ : P₀.B₀ →ₐ[A₀] P₀.B₀) P₀.univ =
        (Quot.mk _ y : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt P₀.B₀) := by sorry
