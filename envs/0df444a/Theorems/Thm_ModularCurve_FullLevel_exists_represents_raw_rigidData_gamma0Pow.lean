-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_represents_raw_rigidData_gamma0Pow
-- name    : ModularCurve.FullLevel.exists_represents_raw_rigidData_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/47b3f1ad-eae2-5f65-9214-e06a0515eb22
-- title:
--   Finite-type representability of raw full-level rigid Weierstrass data
-- statement:
--   Let $A$ be a commutative ring and let $q,\ell,M'$ be natural numbers with $q$ and $\ell$ prime, $M'\neq 0$, $3\le\ell$, and with $\ell$ and $M'$ invertible in $A$. Assume: (hℓ) for every $A$-algebra $T$, every Weierstrass curve $W/T$, every variable change $C$ and every quadruple $D=(x_P,y_P,x_Q,y_Q)$ in $T$, if $D$ is a level-$\ell$ structure on $W$ (both points satisfy the affine Weierstrass equation, $(W.\mathrm{pre}\Psi\,\ell)$ vanishes at $x_P$ and at $x_Q$, and both independence elements $\mathrm{indepElt}$ are units) then the transformed quadruple `D.variableChange C` is a level-$\ell$ structure on $C\bullet W$; (hM) the analogous variable-change stability of [`ModularCurve.IsGamma0PowAt W p k h`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) under $h\mapsto$ `kernelVariableChangeDeg C (gamma0PowDeg p k) h`. Fix a family of relative group laws $\mathcal G$ on the projective models of curves with unit discriminant over $A$-algebras, chord–tangent and with identity at the origin, and a level transport $\mathcal T$ for $\mathcal G$ at $q$ satisfying `IsSectionTransport`; assume moreover that variable changes and coefficient maps of projective models are realised by graded ring maps as in `IsVariableChangeHom` and `IsCoefficientHom`, with the stated inclusion for irrelevant ideals. Then there is a commutative $A$-algebra $C$ of finite type and a raw datum $x_u$ over $C$ for `rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯` — a Weierstrass curve with unit discriminant, a polynomial $h_p$ satisfying `IsGamma0PowAt` for each prime $p\mid M'$ at exponent $\mathrm{ord}_p(M')$, a level-$\ell$ quadruple, and a raw Drinfeld pair forming a Drinfeld basis of level $q$ — such that for every $A$-algebra $T$ and every such raw datum $x$ over $T$ there is exactly one $A$-algebra map $\psi:C\to T$ with $\psi_*x_u=x$.
--
--   This is the representability of the pre-quotient moduli problem of full-level rigid Weierstrass data in the style of Katz–Mazur: the functor of (curve with invertible discriminant, $\Gamma_0(M')$-type cyclic kernel tuple, level-$\ell$ basis data, Drinfeld $\Gamma(q)$-basis) on commutative $A$-algebras is corepresented by an $A$-algebra of finite type. It supplies the representability input for the quotient construction used in [`ModularCurve.FullLevel.exists_levelModuliPackageAbs_isIntegral_adjoin_of_isSectionTransport_of_isNoetherianRing_of_isUnit_two_three_gamma0Pow`](thm.html#ModularCurve.FullLevel.exists_levelModuliPackageAbs_isIntegral_adjoin_of_isSectionTransport_of_isNoetherianRing_of_isUnit_two_three_gamma0Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_represents_raw_rigidData_gamma0Pow.lean

import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
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

universe u

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

theorem ModularCurve.FullLevel.exists_represents_raw_rigidData_gamma0Pow
    (A : Type u) [CommRing A] (q ℓ M' : ℕ) [Fact q.Prime] [Fact ℓ.Prime] [NeZero M']
    (hℓ3 : 3 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'u : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
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
      (xᵤ : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw C),
      ∀ (T : Type u) [CommRing T] [Algebra A T] (x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).Raw T),
        ∃! ψ : C →ₐ[A] T, (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).mapRing ψ xᵤ = x := by sorry
