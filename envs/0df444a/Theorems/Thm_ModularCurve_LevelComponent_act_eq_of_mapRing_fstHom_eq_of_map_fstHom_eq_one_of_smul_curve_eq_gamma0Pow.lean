-- Prove2me | Theorems.Thm_ModularCurve_LevelComponent_act_eq_of_mapRing_fstHom_eq_of_map_fstHom_eq_one_of_smul_curve_eq_gamma0Pow
-- name    : ModularCurve.LevelComponent.act_eq_of_mapRing_fstHom_eq_of_map_fstHom_eq_one_of_smul_curve_eq_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/114440cb-4cb5-566d-b348-cb9cad531c3c
-- title:
--   Infinitesimal rigidity of Γ₀(M') and level-ℓ structures
-- statement:
--   Fix a prime $\ell$ with $3 \le \ell$ and a non-zero natural number $M'$, and a commutative ring $A₀$ together with two compatibility hypotheses: `hℓ`, that for every $A₀$-algebra $T$, every Weierstrass curve $W$ over $T$, every variable change $C$ and every `LevelPData` $D$ over $T$ (a quadruple $x_P,y_P,x_Q,y_Q \in T$), `IsLevelPStructure W ℓ D` implies `IsLevelPStructure (C • W) ℓ (D.variableChange C)`; and `hM`, that likewise `IsGamma0PowAt W p k h` implies `IsGamma0PowAt (C • W) p k (kernelVariableChangeDeg C (gamma0PowDeg p k) h)`. These are exactly the data defining the level component $L =$ `gamma0PowComponent A₀ M' hM` times (`levelPComponent A₀ ℓ hℓ` times `LevelComponent.trivial`), whose objects over $T$ are triples consisting of a family of polynomials $h_p \in T[X]$ indexed by the prime factors of $M'$, a `LevelPData` over $T$, and a point of `PUnit`, the level condition being `IsGamma0PowAt W p (M'.factorization p) (h p)` for each such $p$ together with `IsLevelPStructure W ℓ D`. Let $k$ be a field and $A₀$-algebra in which $\ell$ and $M'$ are non-zero, and let $z, z'$ be raw data for $L$ over the dual numbers $k[\varepsilon]$, each consisting of a Weierstrass curve with unit discriminant and a level structure on it. Assume $z$ and $z'$ have the same image under the map induced by the $A₀$-algebra map $k[\varepsilon] \to k$, $\varepsilon \mapsto 0$, and let $C$ be a variable change over $k[\varepsilon]$ whose reduction modulo $\varepsilon$ is $1$ and with $C \bullet z.\mathrm{curve} = z'.\mathrm{curve}$. Then $C$ carries $z$ to $z'$: the action of $C$ on the raw datum $z$ (variable change on the curve, `kernelVariableChangeDeg` on each $h_p$, `variableChange` on the `LevelPData`) equals $z'$.
--
--   This is the infinitesimal rigidity of level structures of level prime to the residue characteristic: over the dual numbers a variable change that is trivial modulo $\varepsilon$ and matches the two curves automatically matches the level data, so $z$ and $z'$ give the same point of the associated moduli functor. It is used in the study of $k[\varepsilon]$-points of this moduli problem, feeding the construction of algebra homomorphisms out of the dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelComponent_act_eq_of_mapRing_fstHom_eq_of_map_fstHom_eq_one_of_smul_curve_eq_gamma0Pow.lean

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup
  AlgebraicGeometry CategoryTheory NeronModelInfra
attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelComponent.act_eq_of_mapRing_fstHom_eq_of_map_fstHom_eq_one_of_smul_curve_eq_gamma0Pow
    (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) [NeZero M']
    (A₀ : Type) [CommRing A₀]
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (k : Type) [Field k] [Algebra A₀ k] (hℓk : ((ℓ : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
    (z z' : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).Raw (DualNumber k))
    (hzz' : (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).mapRing ((TrivSqZeroExt.fstHom k k k).restrictScalars A₀) z =
      (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).mapRing ((TrivSqZeroExt.fstHom k k k).restrictScalars A₀) z')
    (C : WeierstrassCurve.VariableChange (DualNumber k))
    (hC : C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1) (hCz : C • z.curve = z'.curve) :
    (((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.levelPComponent A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).toRigid).act C z = z' := by sorry
