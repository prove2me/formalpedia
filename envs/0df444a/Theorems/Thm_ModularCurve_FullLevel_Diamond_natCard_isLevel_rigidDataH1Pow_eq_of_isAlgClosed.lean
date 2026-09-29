-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_natCard_isLevel_rigidDataH1Pow_eq_of_isAlgClosed
-- name    : ModularCurve.FullLevel.Diamond.natCard_isLevel_rigidDataH1Pow_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/b9d326b5-4fec-58eb-9148-7731d8e1db3c
-- title:
--   Counting linked Γ₀(M')–Γ₁(ℓ_g)–Γ(q) level structures
-- statement:
--   Fix a commutative ring $A$, a prime $q$, a positive integer $M'$, and a prime $\ell_g$ with $3 \le \ell_g$ and $\ell_g \mid M'$. Assume three variable-change compatibilities, each over all $A$-algebras $T$: `hℓ`, that `IsGamma1Point` is preserved when a Weierstrass curve $W$ and a datum $D=(x_P,y_P,x_Q,y_Q)$ are moved by $C$; `hM`, that `IsGamma0PowAt W p k h` implies `IsGamma0PowAt (C • W) p k` for the transform `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; and `hL`, that $h \mid$ `inLineMulPoly W ℓg n x` implies `kernelVariableChangeDeg C d h` $\mid$ `inLineMulPoly (C • W) ℓg n (u^{-2}(x-r))`. Fix further a family $\mathcal G$ of relative group laws on projective models of unit-discriminant Weierstrass curves over $A$-algebras which is chord–tangent and has the origin as identity, and a transport $\mathcal T$ of raw Drinfeld pairs along $A$-algebra maps and variable changes that respects sections. Let $\Omega$ be an algebraically closed field of characteristic zero which is an $A$-algebra, with $q \ne 0$ in $\Omega$, and let $W_0$ over $\Omega$ have unit discriminant $\Delta$. Then the number of level structures on $W_0$ for the restricted product component is $$\Big(\prod_{p \mid M'} p^{v_p(M')-1}(p+1)\Big)\cdot\big((\ell_g-1)\cdot \#\mathrm{GL}_2(\mathbb{Z}/q)\big).$$ Here a level structure is a triple consisting of a family $h$ indexed by the prime factors $p$ of $M'$ of polynomials over $\Omega$ with `IsGamma0PowAt W₀ p (v_p(M')) (h p)`, a quadruple $D$ with $(x_P,y_P)$ on the affine curve, $(W_0.\mathrm{pre}\Psi\,\ell_g)(x_P)=0$, $x_Q=x_P$, $y_Q=y_P$, and a raw Drinfeld pair whose curve is the projective model of $W_0$ and whose two sections form a Drinfeld basis of level $q$ for $\mathcal G$; subject to the link condition that, $\ell_g$ being a prime factor of $M'$, $h(\ell_g)$ divides `inLineMulPoly W₀ ℓg (ℓg ^ (v_{ℓg}(M') - 1)) x_P`.
--
--   This is the pointwise degree computation for the moduli problem combining a cyclic $\Gamma_0(M')$-datum, a $\Gamma_1(\ell_g)$-point constrained to lie on the cyclic subgroup, and a full Drinfeld $\Gamma(q)$-basis: over an algebraically closed field of characteristic zero a fixed smooth Weierstrass curve carries exactly $\psi(M')(\ell_g-1)\#\mathrm{GL}_2(\mathbb{Z}/q)$ such structures. It feeds the computation of the number of $A$-algebra maps with prescribed $j$-invariant for the corresponding rigid moduli datum, and thence the degree of the associated modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_natCard_isLevel_rigidDataH1Pow_eq_of_isAlgClosed.lean

import Mathlib
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

theorem ModularCurve.FullLevel.Diamond.natCard_isLevel_rigidDataH1Pow_eq_of_isAlgClosed
    (A : Type) [CommRing A]
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg3 : 3 ≤ ℓg) (hℓgM' : ℓg ∣ M')
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
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra A Ω] (hqΩ : ((q : ℕ) : Ω) ≠ 0)
    (W₀ : WeierstrassCurve Ω) (hΔ : IsUnit W₀.Δ) :
    Nat.card {lev : ((((ModularCurve.gamma0PowComponent A M' hM).prod
        ((ModularCurve.gamma1Component A ℓg hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem)))).obj Ω //
        ((((ModularCurve.gamma0PowComponent A M' hM).prod
        ((ModularCurve.gamma1Component A ℓg hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem)))).IsLevel W₀ lev} =
      (∏ p ∈ M'.primeFactors, p ^ (M'.factorization p - 1) * (p + 1)) *
        ((ℓg - 1) * Nat.card (GL (Fin 2) (ZMod q))) := by sorry
