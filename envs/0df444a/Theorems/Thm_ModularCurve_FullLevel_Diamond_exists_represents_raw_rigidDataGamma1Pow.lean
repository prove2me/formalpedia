-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_represents_raw_rigidDataGamma1Pow
-- name    : ModularCurve.FullLevel.Diamond.exists_represents_raw_rigidDataGamma1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/235be584-bc28-5191-a076-c543276b9e10
-- title:
--   Raw Γ₀(M')–Γ₁(ℓ)–Γ(q) data are representable by a finite-type algebra
-- statement:
--   Let $A$ be a commutative ring, let $q$ and $\ell$ be primes with $\ell \ge 3$, and let $M'$ be a nonzero natural number; assume $\ell$ and $M'$ are units in $A$. Fix: a rule `hℓ` asserting that for every $A$-algebra $T$, every Weierstrass curve $W$ over $T$, every change of variables $C$ and every quadruple $D=(x_P,y_P,x_Q,y_Q)$ in $T$, if $D$ is a $\Gamma_1(\ell)$-point of $W$ (that is, $(x_P,y_P)$ satisfies the affine Weierstrass equation, $(W.\mathrm{pre}\Psi\,\ell)(x_P)=0$, and $x_Q=x_P$, $y_Q=y_P$) then the transformed quadruple `D.variableChange C` is a $\Gamma_1(\ell)$-point of $C \bullet W$; a rule `hM` asserting the analogous invariance of `IsGamma0PowAt W p k h` (the two-torsion-kernel condition when $p^k=2$, otherwise the cyclic kernel-generator condition on $h$) under $h \mapsto$ `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; a family of relative group laws $\mathcal G$ on the projective models of discriminant-unit Weierstrass curves which is chord-tangent (realised on field points by an additive, Galois-equivariant evaluation) and has origin as identity; a level transport $\mathcal T$ for $\mathcal G$ at $q$ which is a section transport; and witnesses `hVC`, `hCO` that changes of variables and coefficient maps are realised by graded ring homomorphisms of the projective coordinate rings satisfying the irrelevant-ideal condition and the pinning identities `IsVariableChangeHom`, `IsCoefficientHom`. Then there exist a commutative ring $C$, an $A$-algebra structure on it making $C$ of finite type over $A$, and an element $x_u$ of the raw data of `rigidDataGamma1Pow A ℓ M' q hℓ hM 𝒢 𝒯` over $C$ — a Weierstrass curve with unit discriminant, a family of $\Gamma_0$-type kernel generators indexed by the prime factors $p$ of $M'$ at exponents $M'.\mathrm{factorization}\,p$, a $\Gamma_1(\ell)$-point, and a Drinfeld pair of level $q$ — such that for every $A$-algebra $T$ and every such raw datum $x$ over $T$ there is a unique $A$-algebra homomorphism $\psi : C \to T$ carrying $x_u$ to $x$ under `mapRing ψ`.
--
--   This is the relative representability step for the rigidified (unquotiented) moduli problem of Weierstrass curves with unit discriminant carrying a $\Gamma_0(M')$-tuple of kernel generators, a $\Gamma_1(\ell)$-point and a Drinfeld basis of level $q$: no quotient by changes of variables is taken, so the representing object is an honest finite-type $A$-algebra with a universal datum. It is used by the corresponding representability statement for the $H_1$-variant of the level structure, on the way to the moduli interpretation underlying the modularity-lifting arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_represents_raw_rigidDataGamma1Pow.lean

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

theorem ModularCurve.FullLevel.Diamond.exists_represents_raw_rigidDataGamma1Pow
    (A : Type u) [CommRing A] (q ℓ M' : ℕ) [Fact q.Prime] [Fact ℓ.Prime] [NeZero M']
    (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'u : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
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
      (xᵤ : (rigidDataGamma1Pow A ℓ M' q hℓ hM 𝒢 𝒯).Raw C),
      ∀ (T : Type u) [CommRing T] [Algebra A T] (x : (rigidDataGamma1Pow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T),
        ∃! ψ : C →ₐ[A] T, (rigidDataGamma1Pow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing ψ xᵤ = x := by sorry
