-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_variableChange_map_eq_one_of_eq_act_of_map_residue_eq_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.variableChange_map_eq_one_of_eq_act_of_map_residue_eq_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/90d3c84d-c1c0-5161-9574-ff9704850ff2
-- title:
--   Residual triviality of variable changes at level Γ₁(ℓ_g)
-- statement:
--   Fix natural numbers $q,\ell_g,M'$ with $\ell_g$ prime and $\ell_g \equiv 11 \pmod{12}$, and a commutative ring $A_0$. Assume the three transport hypotheses used to build the rigid datum: `hℓ`, that for every $A_0$-algebra $T$, Weierstrass curve $W$ over $T$, variable change $C$ and level datum $D$ (a quadruple $x_P,y_P,x_Q,y_Q$ in $T$), the conditions of `IsGamma1Point` for $(W,\ell_g,D)$ — the affine equation at $(x_P,y_P)$, vanishing of $W.\mathrm{pre}\Psi_{\ell_g}$ at $x_P$, and $x_Q=x_P$, $y_Q=y_P$ — are inherited by $C\cdot W$ and the translated datum $D^{C}$; `hM`, that `IsGamma0PowAt` at $(p,k)$ is likewise inherited by $C\cdot W$ with $h$ replaced by its $C$-twist `kernelVariableChangeDeg`; and `hL`, that divisors of `inLineMulPoly` transport to divisors of the twisted polynomial after the substitution $x \mapsto u^{-2}(x-r)$. Let $\mathcal G$ be group laws over $A_0$ and $\mathcal T$ a level transport at level $q$, so that `rigidDataH1Pow` is defined. Let $T$ be an $A_0$-algebra, $k$ a field, $\mathrm{res}_T : T \to k$ a ring homomorphism with $\ell_g \ne 0$ in $k$, and let $x,y$ be raw points of `rigidDataH1Pow` over $T$ (each consisting of a Weierstrass curve with unit discriminant, a level object and a proof that it is a level structure). If $y$ is obtained from $x$ by the action of a variable change $C$, and if the curves of $x$ and $y$ as well as their $\Gamma_1$-components $x.\mathrm{level}.2.1$, $y.\mathrm{level}.2.1$ agree after applying $\mathrm{res}_T$ coordinatewise, then the pushed-forward variable change $C \bmod \ker(\mathrm{res}_T)$ is the identity.
--
--   This is the rigidity statement for the moduli problem of level $\Gamma_0(M') \cap \Gamma_1(\ell_g)$ together with a Drinfeld $\Gamma(q)$-structure: a change of variables which residually preserves both the curve and its $\ell_g$-torsion point is residually trivial. It is used in the construction of the associated level moduli package, in the statements producing algebra maps from raw data with prescribed Drinfeld bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_variableChange_map_eq_one_of_eq_act_of_map_residue_eq_rigidDataH1Pow.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.FullLevel.variableChange_map_eq_one_of_eq_act_of_map_residue_eq_rigidDataH1Pow
    (q ℓg M' : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11)
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
    (𝒢 : GroupLaws A₀) (𝒯 : LevelTransport A₀ 𝒢 q)
    (T : Type) [CommRing T] [Algebra A₀ T] (k : Type) [Field k] (resT : T →+* k) (hℓk : ((ℓg : ℕ) : k) ≠ 0)
    (x y : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T) (C : WeierstrassCurve.VariableChange T)
    (hC : y = (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).act C x)
    (hcurve : y.curve.map resT = x.curve.map resT)
    (hlev : y.level.2.1.map resT = x.level.2.1.map resT) :
    C.map resT = 1 := by sorry
