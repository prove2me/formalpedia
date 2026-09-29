-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_of_ne_two_gamma0Pow
-- name    : ModularCurve.FullLevel.map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_of_ne_two_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/f8726406-bce1-5c29-b1fe-4b7ee90601d6
-- title:
--   Surjectivity of full-level points along nilpotent thickenings
-- statement:
--   Fix a prime $q \neq 2$, a prime $\ell$ with $3 \le \ell$, a nonzero natural number $M'$, and a commutative ring $A_0$. Assume the two equivariance hypotheses needed to build the level datum: `hℓ`, that for every $A_0$-algebra $T$, every Weierstrass curve $W$ over $T$, every variable change $C$ and every `LevelPData` $D$ over $T$ (a quadruple $x_P, y_P, x_Q, y_Q$), the conditions `IsLevelPStructure W ℓ D` — that $(x_P,y_P)$ and $(x_Q,y_Q)$ satisfy the affine equation of $W$, that $(W.\mathrm{preΨ}\,\ell)$ vanishes at $x_P$ and at $x_Q$, and that the two elements $\mathrm{indepElt}\,W\,\ell\,x_P\,x_Q$ and $\mathrm{indepElt}\,W\,\ell\,x_Q\,x_P$ are units — are preserved by passing to $C \bullet W$ and $D$ transported by $C$; and `hM`, that `IsGamma0PowAt W p k h` is likewise preserved on replacing $W$ by $C \bullet W$ and $h$ by `kernelVariableChangeDeg C (gamma0PowDeg p k) h`, where `IsGamma0PowAt W p k h` asks, when $p^k = 2$, that $\deg h \le 1$, that the coefficient of $h$ in degree $1$ be $1$ and that $h \mid W.\Psi_2^2$, and otherwise that $\deg h \le \varphi(p^k)/2$, that the coefficient of $h$ in degree $\varphi(p^k)/2$ be $1$, that $h \cdot W.\mathrm{preΨ}(p^{k-1})$ divide $W.\mathrm{preΨ}(p^{k})$, and that $h$ divide $W.\mathrm{smulNumerator}\,a\,(\varphi(p^k)/2)\,h$ for all $a$ with $2 \le a \le (p^k-1)/2$ and $p \nmid a$. Fix further a family of group laws $\mathcal{G}$ on the projective Weierstrass models over $A_0$-algebras which is chord-tangent and has the origin as identity, and a level transport $\mathcal{T}$ for $\mathcal{G}$ at $q$ which is a section transport. Let $\pi : C \to C'$ be a surjective homomorphism of $A_0$-algebras whose kernel satisfies $(\ker \pi)^n = 0$ for some $n$, and suppose $q$, $\ell$ and $M'$ are units in $C$. Then the map induced by $\pi$ on the points of the level moduli datum attached to `rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯` is surjective; concretely, every class over $C'$ of a tuple consisting of a Weierstrass curve with unit discriminant, a family of polynomials indexed by the prime factors $p$ of $M'$ satisfying `IsGamma0PowAt` at $(p, v_p(M'))$, a level-$\ell$ structure and a raw Drinfeld pair which is a Drinfeld basis of level $q$ for $\mathcal{G}$, modulo variable changes, is the image of such a class over $C$. The hypothesis $3 \le \ell$ is used only through $\ell \neq 2$.
--
--   This is the formal-lifting (infinitesimal surjectivity) property of the full level structure $\Gamma_0(M') \times \Gamma(\ell) \times \Gamma_{\mathrm{Drinfeld}}(q)$ moduli problem on elliptic curves, in the style of the étale lifting of level structures of Katz–Mazur, away from the residue characteristics dividing $q\ell M'$. It feeds the formal smoothness of the associated local rings and the smoothness of the base change of the full-level moduli package to a fraction field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_of_ne_two_gamma0Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.FullLevel.map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_of_ne_two_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) [NeZero M']
    (A₀ : Type) [CommRing A₀]
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    {C C' : Type} [CommRing C] [Algebra A₀ C] [CommRing C'] [Algebra A₀ C']
    (π : C →ₐ[A₀] C') (hπ : Function.Surjective π) (hnil : ∃ n : ℕ, RingHom.ker π.toRingHom ^ n = ⊥)
    (hqC : IsUnit ((q : ℕ) : C)) (hℓC : IsUnit ((ℓ : ℕ) : C)) (hM'C : IsUnit ((M' : ℕ) : C)) :
    Function.Surjective ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map π) := by sorry
