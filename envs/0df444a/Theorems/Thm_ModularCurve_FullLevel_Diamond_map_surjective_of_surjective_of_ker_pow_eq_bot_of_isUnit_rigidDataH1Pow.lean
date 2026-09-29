-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/87a9a2c9-345a-5e85-bbec-f2140a84dad1
-- title:
--   Lifting H₁ moduli points along nilpotent-kernel surjections
-- statement:
--   Fix a prime $q$, natural numbers $\ell_g$ and $M'$ with $\ell_g$ prime, $\ell_g \ge 5$ and $M' \neq 0$, and a commutative ring $A_0$. Assume three variable-change compatibilities, each quantified over all $A_0$-algebras $T$: `hℓ`, that `IsGamma1Point W ℓg D` (i.e. $(x_P,y_P)$ satisfies the affine Weierstrass equation, $\mathrm{pre}\Psi_{\ell_g}$ vanishes at $x_P$, and $x_Q = x_P$, $y_Q = y_P$) is preserved on passing to $C \bullet W$ and `D.variableChange C`; `hM`, that `IsGamma0PowAt W p k h` is preserved on passing to $C \bullet W$ and `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; and `hL`, that a divisor $h$ of `inLineMulPoly W ℓg n x` transforms to a divisor `kernelVariableChangeDeg C d h` of `inLineMulPoly (C • W) ℓg n (u^{-2}(x - r))`. Fix further group laws $\mathcal G$ on the projective models over all $A_0$-algebras which are chord–tangent (`IsChordTangent`) and have the origin as identity section (`IsOriginIdentity`), and a level transport $\mathcal T$ of raw Drinfeld pairs of level $q$ satisfying `IsSectionTransport`. Let $C$, $C'$ be $A_0$-algebras and $\pi : C \to C'$ a surjective $A_0$-algebra map some power of whose kernel is $\bot$, and suppose $q$, $\ell_g$ and $M'$ are units in $C$. Then the map induced by $\pi$ on the points of the moduli datum `(rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum` is surjective: every variable-change class over $C'$ of a Weierstrass curve $W'$ with unit discriminant together with a family $h'$ of monic-normalised $\Gamma_0(p^{v_p(M')})$-kernel polynomials indexed by the prime factors of $M'$, a $\Gamma_1(\ell_g)$-point $D'$, a Drinfeld basis $z'$ of level $q$ for $\mathcal G$, and the link condition that $h'_{\ell_g}$ divides `inLineMulPoly W' ℓg (ℓg ^ (M'.factorization ℓg - 1)) D'.xP` when $\ell_g \mid M'$, is the image of such a class over $C$.
--
--   This is the infinitesimal lifting (formal smoothness) input for the moduli problem of level $H_1 = \Gamma_0(M') \cap \Gamma_1(\ell_g)$ rigidified by a Drinfeld basis of level $q$: points lift along surjections with nilpotent kernel. It is used in the proofs that the associated moduli ring is formally smooth at primes off the bad locus and that its generic fibre is smooth.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_rigidDataH1Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
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

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.FullLevel.Diamond.map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (ℓg M' : ℕ) (hℓg : ℓg.Prime) (hℓg5 : 5 ≤ ℓg) [NeZero M']
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
    {C C' : Type} [CommRing C] [Algebra A₀ C] [CommRing C'] [Algebra A₀ C']
    (π : C →ₐ[A₀] C') (hπ : Function.Surjective π) (hnil : ∃ n : ℕ, RingHom.ker π.toRingHom ^ n = ⊥)
    (hqC : IsUnit ((q : ℕ) : C)) (hℓC : IsUnit ((ℓg : ℕ) : C)) (hM'C : IsUnit ((M' : ℕ) : C)) :
    Function.Surjective ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map π) := by sorry
