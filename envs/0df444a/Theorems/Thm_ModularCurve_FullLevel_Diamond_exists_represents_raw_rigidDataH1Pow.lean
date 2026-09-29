-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_represents_raw_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.exists_represents_raw_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/adf64c7f-a7b5-5f3e-a18d-c0dd11f2a1aa
-- title:
--   Representability of raw H₁-level data over A
-- statement:
--   Let $A$ be a commutative ring and $q,\ell,M'$ natural numbers with $q$ and $\ell$ prime, $M'$ nonzero, $\ell\ge 3$, and both $\ell$ and $M'$ invertible in $A$. Assume three transport hypotheses, each for every commutative $A$-algebra $T$: that a $\Gamma_1(\ell)$-point of a Weierstrass curve $W$ over $T$ (a pair of coordinates $P=(x_P,y_P)$, $Q=(x_Q,y_Q)$ with $Q=P$, $P$ on the affine curve and $(\mathrm{pre}\Psi_\ell)(x_P)=0$) transports along a variable change $C$ to a $\Gamma_1(\ell)$-point of $C\bullet W$; that `IsGamma0PowAt W p k h` is preserved by passing to `kernelVariableChangeDeg C (gamma0PowDeg p k) h` on $C\bullet W$; and that a divisor $h$ of `inLineMulPoly W ℓ n x` yields the divisor `kernelVariableChangeDeg C d h` of `inLineMulPoly (C • W) ℓ n (u^{-2}(x-r))`. Assume further a family $\mathcal G$ of relative group laws on the projective models of curves with unit discriminant which is chord-tangent and has the origin as identity section, a level transport $\mathcal T$ for Drinfeld $\Gamma(q)$-pairs satisfying `IsSectionTransport`, and the existence, for every $W$ over $T$, of graded ring homomorphisms of projective-model rings realising variable changes and coefficient changes, each with the irrelevant-ideal condition. Then there is an $A$-algebra $C$ of finite type and a raw datum $x_u$ over $C$ for `rigidDataH1Pow A ℓ M' q hℓ hM hL 𝒢 𝒯` — a curve with unit discriminant, a family of $\Gamma_0(p^{v_p(M')})$-kernel polynomials indexed by the prime factors of $M'$, a $\Gamma_1(\ell)$-point, a Drinfeld $\Gamma(q)$-basis, and the link condition that the $\ell$-component divides `inLineMulPoly W ℓ (ℓ^(v_ℓ(M')-1)) x_P` when $\ell \mid M'$ — such that for every commutative $A$-algebra $T$ and every raw datum $x$ over $T$ there is a unique $A$-algebra homomorphism $\psi : C \to T$ with $\psi_* x_u = x$.
--
--   This is the representability of the rigidified moduli functor of elliptic curves with $\Gamma_0(M')$-, $\Gamma_1(\ell)$- and Drinfeld $\Gamma(q)$-structure, in the Katz–Mazur style: the functor of raw $H_1$-level data is affine and of finite type over $A$. It is the representability input to the construction of the level moduli package obtained by dividing out the variable-change action, and is deduced from the corresponding statement for the unlinked data by adding the divisibility link condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_represents_raw_rigidDataH1Pow.lean

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

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

theorem ModularCurve.FullLevel.Diamond.exists_represents_raw_rigidDataH1Pow
    (A : Type u) [CommRing A] (q ℓ M' : ℕ) [Fact q.Prime] [Fact ℓ.Prime] [NeZero M']
    (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'u : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.FiniteType A C)
      (xᵤ : (rigidDataH1Pow A ℓ M' q hℓ hM hL 𝒢 𝒯).Raw C),
      ∀ (T : Type u) [CommRing T] [Algebra A T] (x : (rigidDataH1Pow A ℓ M' q hℓ hM hL 𝒢 𝒯).Raw T),
        ∃! ψ : C →ₐ[A] T, (rigidDataH1Pow A ℓ M' q hℓ hM hL 𝒢 𝒯).mapRing ψ xᵤ = x := by sorry
