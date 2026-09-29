-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_forall_eq_map_dualNumber_smul_of_trivial_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.exists_forall_eq_map_dualNumber_smul_of_trivial_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/10d4c908-2e95-50b4-8b62-3850d358456d
-- title:
--   Tangent line of the Γ₀(M')∩Γ₁(ℓ) Weierstrass moduli problem
-- statement:
--   Fix a prime $\ell$ with $5\le\ell$, a nonzero natural number $M'$, and a commutative ring $A_0$. Three equivariance hypotheses are assumed for all $A_0$-algebras $T$, all Weierstrass curves $W$ over $T$ and all variable changes $C$: `hℓ`, that `IsGamma1Point W ℓ D` (the point $(x_P,y_P)$ of $D$ satisfies the affine equation, $(W.preΨ ℓ)(x_P)=0$, and $(x_Q,y_Q)=(x_P,y_P)$) is preserved by passing to $C\bullet W$ and the transported datum `D.variableChange C`; `hM`, that `IsGamma0PowAt W p k h` is preserved by passing to $C\bullet W$ and `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; and `hL`, that a divisibility $h \mid$ `inLineMulPoly W ℓ n x` gives `kernelVariableChangeDeg C d h` $\mid$ `inLineMulPoly (C • W) ℓ n` $(u^{-2}(x-r))$, for every degree $d$. Let $k$ be a field and an $A_0$-algebra in which $\ell$ and $M'$ are nonzero. Consider the level component obtained as the product of `gamma0PowComponent A₀ M' hM` (families $h$ indexed by the prime factors $p$ of $M'$, with `IsGamma0PowAt W p (M'.factorization p) (h p)`) with `gamma1Component A₀ ℓ hℓ` and the trivial component, restricted by the link condition `IsGamma1Link W ℓ M' h D`, i.e. if $\ell \mid M'$ then $h_\ell$ divides `inLineMulPoly W ℓ (ℓ ^ (M'.factorization ℓ - 1)) D.xP`; its associated rigid Weierstrass data and level moduli datum have, over an $A_0$-algebra $T$, as points the variable-change orbits of Weierstrass curves over $T$ with unit discriminant equipped with such a level structure. The assertion is that for every point $x_0$ over $k$ there is a point $y_1$ over the dual numbers $k[\varepsilon]$ such that: $y_1$ maps to $x_0$ under $\varepsilon\mapsto 0$; $y_1$ differs from the image of $x_0$ under $k\to k[\varepsilon]$; and every point $y$ over $k[\varepsilon]$ lying above $x_0$ equals the image of $y_1$ under the map of dual numbers induced by $\varepsilon\mapsto c\varepsilon$ for some $c\in k$.
--
--   This is the tangent-space computation for the rigidified Weierstrass moduli problem of level $\Gamma_0(M')\cap\Gamma_1(\ell)$ (with trivial third slot): the fibre of $\mathcal{M}(k[\varepsilon])\to\mathcal{M}(k)$ over a $k$-point is a line, swept out by a single nonconstant deformation under the rescalings $\varepsilon\mapsto c\varepsilon$. It feeds the existence statement [`ModularCurve.FullLevel.Diamond.exists_pt_dualNumber_map_fstHom_eq_ne_map_inlAlgHom_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.exists_pt_dualNumber_map_fstHom_eq_ne_map_inlAlgHom_rigidDataH1Pow) and the identification of complete local rings of the moduli problem with power series rings in [`ModularCurve.LevelModuliPackageAbs.nonempty_algEquiv_powerSeries_of_factorsThrough_trivial_rigidDataH1Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.nonempty_algEquiv_powerSeries_of_factorsThrough_trivial_rigidDataH1Pow), which together give smoothness of relative dimension one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_forall_eq_map_dualNumber_smul_of_trivial_rigidDataH1Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.FullLevel.Diamond.exists_forall_eq_map_dualNumber_smul_of_trivial_rigidDataH1Pow
    (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) [NeZero M']
    (A₀ : Type) [CommRing A₀]
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (k : Type) [Field k] [Algebra A₀ k] (hℓk : ((ℓ : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
    (x₀ : ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.Pt k) :
    ∃ y₁ : ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.Pt (DualNumber k),
      ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.map
          ((TrivSqZeroExt.fstHom k k k).restrictScalars A₀) y₁ = x₀ ∧
      y₁ ≠ ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.map
          ((TrivSqZeroExt.inlAlgHom k k k).restrictScalars A₀) x₀ ∧
      ∀ y : ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.Pt (DualNumber k),
        ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.map
            ((TrivSqZeroExt.fstHom k k k).restrictScalars A₀) y = x₀ →
        ∃ c : k, y = ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.map
            ((TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).restrictScalars A₀) y₁ := by sorry
