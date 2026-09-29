-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_two_mul_natCard_pt_jOf_eq_eq_natCard_isLevel_rigidDataPow_of_isAlgClosed
-- name    : ModularCurve.FullLevel.two_mul_natCard_pt_jOf_eq_eq_natCard_isLevel_rigidDataPow_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/fa5a2d20-0e40-580e-8eca-c2d1395f2de5
-- title:
--   Twice the j-fibre equals the level data on W₀
-- statement:
--   Fix a commutative ring $A$, a prime $q$, a nonzero natural number $M'$, and a prime $\ell\ge 3$. Assume two equivariance hypotheses for $A$-algebras $T$: that $\ell$-level data satisfying [`ModularCurve.IsLevelPStructure`](def/ModularCurve_KatzLevelP.html#L104) for $W$ (the two points lie on $W$, their abscissae are roots of $W.\mathrm{pre}\Psi_\ell$, and both `indepElt` expressions are units) remain so for $C\bullet W$ after `LevelPData.variableChange`, and that [`ModularCurve.IsGamma0PowAt W p k h`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) (`IsTwoKernel` if $p^k=2$, otherwise `IsCyclicGenKernel`) is preserved on passing to $C\bullet W$ and `kernelVariableChangeDeg C (gamma0PowDeg p k) h`. Fix group laws $\mathcal{G}$ on projective Weierstrass models over $A$-algebras which are chord–tangent and have the origin as identity, and a level transport $\mathcal{T}$ for Drinfeld pairs at $q$ which is a section transport. Let $\Omega$ be an algebraically closed field of characteristic zero with an $A$-algebra structure in which $\ell\ne 0$, and let $W_0/\Omega$ be a Weierstrass curve with $\Delta$ a unit, with $j(W_0)=t$, $t\ne 0$ and $t\ne 1728$. Then twice the number of points $x$ of the moduli datum of `rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯` over $\Omega$ — classes of pairs (curve with unit discriminant, level datum) modulo variable change — with $j$-invariant $t$ equals the number of level data $\mathrm{lev}$ over $\Omega$ for the triple product component (one monic kernel polynomial for each prime factor of $M'$, an $\ell$-level point pair, a raw Drinfeld pair) that are level structures on $W_0$ itself.
--
--   This is the orbit-counting step identifying fibres of the $j$-map on a full-level Weierstrass moduli problem with the set of level structures on one fixed model: away from $j=0,1728$ the variable-change stabiliser of $W_0$ has order $2$ and acts freely on the level data, so each isomorphism class over $\Omega$ accounts for exactly two level structures on $W_0$. It is used in establishing the cardinality of the $j$-fibres over a transcendental value for the $\Gamma_0(M')$-power component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_two_mul_natCard_pt_jOf_eq_eq_natCard_isLevel_rigidDataPow_of_isAlgClosed.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.two_mul_natCard_pt_jOf_eq_eq_natCard_isLevel_rigidDataPow_of_isAlgClosed
    (A : Type) [CommRing A]
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra A Ω] (hℓΩ : ((ℓ : ℕ) : Ω) ≠ 0)
    (W₀ : WeierstrassCurve Ω) (hΔ : IsUnit W₀.Δ) (t : Ω) (hj : W₀.jOfUnit hΔ = t) (ht0 : t ≠ 0) (ht : t ≠ 1728) :
    2 * Nat.card {x : (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.Pt Ω //
        (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.jOf x = t} =
      Nat.card {lev : ((ModularCurve.gamma0PowComponent A M' hM).prod
          ((ModularCurve.levelPComponent A ℓ hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).obj Ω //
        ((ModularCurve.gamma0PowComponent A M' hM).prod
          ((ModularCurve.levelPComponent A ℓ hℓ).prod (WeierstrassCurve.DrinfeldGlobal.levelComponent A 𝒢 q 𝒯))).IsLevel W₀ lev} := by sorry
