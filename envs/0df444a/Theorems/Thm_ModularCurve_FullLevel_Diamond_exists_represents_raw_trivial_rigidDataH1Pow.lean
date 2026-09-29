-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_exists_represents_raw_trivial_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.exists_represents_raw_trivial_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/c0853a6e-dfae-5f5b-bfb8-f46e8058919b
-- title:
--   Representability of the raw Γ₀(N)–Γ₁(ℓ) Weierstrass functor
-- statement:
--   Let $A$ be a commutative ring, $\ell$ a prime and $N$ a nonzero natural number, and assume $5 \le \ell$ and that the images of $\ell$ and of $N$ in $A$ are units. Assume three transport rules, each for all commutative $A$-algebras $T$: that a $\Gamma_1(\ell)$-point datum $D = (x_P,y_P,x_Q,y_Q)$ for $W$ (meaning $(x_P,y_P)$ satisfies the affine equation of $W$, $(W.\mathrm{pre}\Psi\,\ell)(x_P)=0$, $x_Q = x_P$ and $y_Q = y_P$) is carried by a variable change $C$ to such a datum for $C \bullet W$; that the predicate `IsGamma0PowAt W p k h` is carried to `IsGamma0PowAt (C • W) p k` of `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; and that $h \mid$ `inLineMulPoly W ℓ n x` implies `kernelVariableChangeDeg C d h` $\mid$ `inLineMulPoly (C • W) ℓ n (u^{-2}(x-r))` for the data of $C$. Consider the level component obtained from the product of the $\Gamma_0$-power component for $N$, the $\Gamma_1(\ell)$ component and the trivial component, restricted to those data satisfying `IsGamma1Link W ℓ N`, that is: whenever $\ell \mid N$, the $\ell$-component polynomial divides `inLineMulPoly W ℓ (ℓ^(N.factorization ℓ - 1)) D.xP`. Its raw data over $T$ are quadruples consisting of a Weierstrass curve over $T$ with unit discriminant, a family of polynomials indexed by the prime factors $p$ of $N$ which are $\Gamma_0(p^{v_p(N)})$-kernel data for the curve, a $\Gamma_1(\ell)$-point datum, and the link condition. The assertion is that there exist a commutative ring $C$ which is an $A$-algebra of finite type and a raw datum $x_u$ over $C$ such that for every commutative $A$-algebra $T$ and every raw datum $x$ over $T$ there is a unique $A$-algebra homomorphism $\psi : C \to T$ whose pushforward of $x_u$ (applying $\psi$ to the curve coefficients, the polynomials and the point coordinates) equals $x$.
--
--   This is the representability of the raw (pre-quotient, before passage to variable-change orbits) moduli functor of Weierstrass curves with unit discriminant equipped with $\Gamma_0(N)$-kernel data, a $\Gamma_1(\ell)$-point and the compatibility link between them, the Drinfeld slot being replaced by the trivial component. It feeds the construction of the corresponding level moduli package, [`ModularCurve.FullLevel.Diamond.exists_levelModuliPackageAbs_trivial_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.exists_levelModuliPackageAbs_trivial_rigidDataH1Pow), and rests on the universal Weierstrass ring with unit discriminant together with the representability of $\Gamma_0$-power kernel tuples.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_represents_raw_trivial_rigidDataH1Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.FullLevel.Diamond.exists_represents_raw_trivial_rigidDataH1Pow
    (A : Type u) [CommRing A] (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hℓ5 : 5 ≤ ℓ) (hℓA : IsUnit ((ℓ : ℕ) : A)) (hNA : IsUnit ((N : ℕ) : A))
    (hℓ : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓ D →
        ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C))
    (hN : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type u) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓ n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r))) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.FiniteType A C)
      (xᵤ : ((((ModularCurve.gamma0PowComponent A N hN).prod
            ((ModularCurve.gamma1Component A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).restrict
            (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
            (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
            (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).Raw C),
      ∀ (T : Type u) [CommRing T] [Algebra A T]
        (x : ((((ModularCurve.gamma0PowComponent A N hN).prod
            ((ModularCurve.gamma1Component A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).restrict
            (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
            (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
            (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).Raw T),
        ∃! ψ : C →ₐ[A] T,
          ((((ModularCurve.gamma0PowComponent A N hN).prod
            ((ModularCurve.gamma1Component A ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A)))).restrict
            (fun W x => ModularCurve.IsGamma1Link W ℓ N x.1 x.2.1)
            (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
            (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).mapRing ψ xᵤ = x := by sorry
