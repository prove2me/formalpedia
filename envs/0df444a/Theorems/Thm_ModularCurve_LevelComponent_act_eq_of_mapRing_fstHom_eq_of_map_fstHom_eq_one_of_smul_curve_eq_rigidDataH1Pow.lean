-- Prove2me | Theorems.Thm_ModularCurve_LevelComponent_act_eq_of_mapRing_fstHom_eq_of_map_fstHom_eq_one_of_smul_curve_eq_rigidDataH1Pow
-- name    : ModularCurve.LevelComponent.act_eq_of_mapRing_fstHom_eq_of_map_fstHom_eq_one_of_smul_curve_eq_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/affee3b7-e34c-5a1a-9778-f8b828772086
-- title:
--   Infinitesimal rigidity of the Γ₀(M')∩Γ₁(ℓ_g) level datum
-- statement:
--   Fix natural numbers $\ell_g$, $M'$ with $\ell_g$ prime, $\ell_g \equiv 11 \pmod{12}$ and $M'$ nonzero, and a commutative ring $A_0$. Three transport hypotheses are assumed, for all $A_0$-algebras $T$, Weierstrass curves $W/T$ and variable changes $C$: `hℓ`, that `IsGamma1Point W ℓg D` (the point $(D.xP, D.yP)$ lies on the affine equation of $W$, $D.xP$ is a root of $W.preΨ\ \ell_g$, and $D.xQ = D.xP$, $D.yQ = D.yP$) passes to $C \bullet W$ and `D.variableChange C`; `hM`, that `IsGamma0PowAt W p k h` passes to $C \bullet W$ and `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; and `hL`, that $h \mid$ `inLineMulPoly W ℓg n x` implies `kernelVariableChangeDeg C d h` $\mid$ `inLineMulPoly (C • W) ℓg n` $(u^{-2}(x - r))$. Let $L$ be the level component whose data over $T$ are tuples $(h, (D, \ast))$ with $h$ a polynomial for each prime factor of $M'$ and $D$ a `LevelPData T`, the level condition being: `IsGamma0PowAt W p (M'.factorization p) (h p)` for each prime $p \mid M'$, `IsGamma1Point W ℓg D`, and the link condition `IsGamma1Link W ℓg M' h D`, i.e. if $\ell_g \mid M'$ then $h(\ell_g)$ divides `inLineMulPoly W ℓg` $(\ell_g^{v_{\ell_g}(M')-1})\, (D.xP)$; maps and variable-change actions are componentwise, via `Polynomial.map` and `kernelVariableChangeDeg`, `LevelPData.map` and `LevelPData.variableChange`. Let $k$ be a field and $A_0$-algebra in which $\ell_g$ and $M'$ are nonzero. Let $z, z'$ be raw data for $L$ over the dual numbers $k[\varepsilon]$, i.e. Weierstrass curves with unit discriminant together with level data satisfying the above, and assume $z$ and $z'$ have the same image under the map induced by $\varepsilon \mapsto 0$. Then for every variable change $C$ over $k[\varepsilon]$ reducing to $1$ modulo $\varepsilon$ and satisfying $C \bullet z.curve = z'.curve$, one has `act C z = z'`, so $C$ carries the full datum $z$ to $z'$.
--
--   This is the infinitesimal rigidity statement for the rigid Weierstrass datum at level $H_1 = \Gamma_0(M') \cap \Gamma_1(\ell_g)$: a variable change over the dual numbers that is trivial modulo $\varepsilon$ and matches the underlying curves automatically matches the level structures as well, so that $z$ and $z'$ define the same $k[\varepsilon]$-point of the associated moduli functor. It is used in the construction of algebra homomorphisms into dual numbers for the corresponding level moduli package, where the unique infinitesimal liftings of the $\Gamma_0$-kernel polynomials and of the $\Gamma_1(\ell_g)$-point supply the required identifications.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelComponent_act_eq_of_mapRing_fstHom_eq_of_map_fstHom_eq_one_of_smul_curve_eq_rigidDataH1Pow.lean

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup
  AlgebraicGeometry CategoryTheory NeronModelInfra

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelComponent.act_eq_of_mapRing_fstHom_eq_of_map_fstHom_eq_one_of_smul_curve_eq_rigidDataH1Pow
    (ℓg M' : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) [NeZero M']
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
    (k : Type) [Field k] [Algebra A₀ k] (hℓk : ((ℓg : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
    (z z' : ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓg hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).Raw (DualNumber k))
    (hzz' : ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓg hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).mapRing ((TrivSqZeroExt.fstHom k k k).restrictScalars A₀) z =
      ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓg hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).mapRing ((TrivSqZeroExt.fstHom k k k).restrictScalars A₀) z')
    (C : WeierstrassCurve.VariableChange (DualNumber k))
    (hC : C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1) (hCz : C • z.curve = z'.curve) :
    ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓg hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓg M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).act C z = z' := by sorry
