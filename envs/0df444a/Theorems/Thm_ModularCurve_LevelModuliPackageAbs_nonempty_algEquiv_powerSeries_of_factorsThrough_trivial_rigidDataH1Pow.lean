-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_nonempty_algEquiv_powerSeries_of_factorsThrough_trivial_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.nonempty_algEquiv_powerSeries_of_factorsThrough_trivial_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/c2fb7808-0e9a-5fac-8d60-443ed24eb937
-- title:
--   Completed stalk of the linked Γ₀(M')×Γ₁(ℓ) package is W₀[[t]]
-- statement:
--   Fix a prime $q$, a prime $\ell$ with $5\le\ell$, a nonzero $M'$, and a commutative ring $A_0$, together with three transport hypotheses, each quantified over all $A_0$-algebras $T$, Weierstrass curves $W/T$ and variable changes $C$: that the conditions defining a $\Gamma_1(\ell)$-point of $W$ (a pair $(x_P,y_P)$ on the affine Weierstrass equation with $\mathrm{pre}\Psi_\ell(x_P)=0$, and $(x_Q,y_Q)=(x_P,y_P)$) are preserved by $C$ acting on the level-$p$ data; that the conditions `IsGamma0PowAt` (for $p^k=2$ a monic linear divisor of $\Psi_2^{\,2}$, otherwise a monic generator of degree $\varphi(p^k)/2$ with $h\cdot\mathrm{pre}\Psi_{p^{k-1}}\mid \mathrm{pre}\Psi_{p^k}$ and the prescribed divisibilities of the $\mathrm{smulNumerator}$s) are preserved by $h\mapsto u^{-2d}\,h(u^2X+r)$; and that divisibility of `inLineMulPoly` is preserved likewise. Let $L$ be the level component whose data over $T$ consist of a family $h_p\in T[X]$ indexed by the prime factors of $M'$, a level-$p$ datum $D$ and a point of the trivial component, the level condition asking that each $h_p$ satisfy `IsGamma0PowAt` at $p^{v_p(M')}$, that $D$ be a $\Gamma_1(\ell)$-point, and the link condition: if $\ell\mid M'$ then $h_\ell$ divides $\mathrm{inLineMulPoly}(W,\ell,\ell^{v_\ell(M')-1},x_P)$. Let $P$ be a fine moduli package over $A_0$ for the associated moduli datum, whose points over $T$ are the classes, modulo variable change, of Weierstrass curves over $T$ with unit discriminant equipped with such level data, with $j$-invariant as distinguished function; thus $P$ consists of an $A_0$-algebra $B_0$, a universal point, and for each $A_0$-algebra $T$ a unique $A_0$-algebra map $B_0\to T$ carrying the universal point to any given point. Let $x$ be a representative whose class is the universal point. Let $R_0$ be a Noetherian local ring, complete for its maximal-ideal adic topology, an $A_0$-algebra, with $\iota:B_0\to R_0$ an $A_0$-algebra map; let $k$ be a field in which $\ell$ and $M'$ are nonzero and $\mathrm{res}_R:R_0\to k$ a surjection with kernel the maximal ideal. Let $W_0$ be a complete discrete valuation domain with maximal ideal $(q)$ and a surjection $\mathrm{res}_0:W_0\to k$ with kernel its maximal ideal, with $R_0$ a $W_0$-algebra, $W_0$ an $A_0$-algebra, the scalar tower compatible, and $\mathrm{res}_R\circ(\text{structure map})=\mathrm{res}_0$. Assume finally the factorisation property: for every Artinian local $A_0$- and $W_0$-algebra $T$ in the tower, every surjection $\mathrm{res}_T:T\to k$ with kernel the maximal ideal compatible with $\mathrm{res}_0$, and every $A_0$-algebra map $\varphi:B_0\to T$ with $\mathrm{res}_T\circ\varphi=\mathrm{res}_R\circ\iota$, there is a unique $W_0$-algebra map $\Phi:R_0\to T$ with $\mathrm{res}_T\circ\Phi=\mathrm{res}_R$ and $\Phi\circ\iota=\varphi$. Then the type of $W_0$-algebra isomorphisms $R_0\simeq W_0[[X]]$ is nonempty.
--
--   This is the smoothness of relative dimension one of the rigid level structure "$\Gamma_0(M')$-tuple together with a linked $\Gamma_1(\ell)$-point", in the form that the complete local ring at a closed point with residue field $k$ is a one-variable power series ring over the unramified complete discrete valuation ring $W_0$. It is used in the construction of the local rings with an adjoined root of a power series that support the arguments at the chosen level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_nonempty_algEquiv_powerSeries_of_factorsThrough_trivial_rigidDataH1Pow.lean

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

open ModularCurve IsLocalRing

theorem ModularCurve.LevelModuliPackageAbs.nonempty_algEquiv_powerSeries_of_factorsThrough_trivial_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) [NeZero M']
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
    (P : LevelModuliPackageAbs A₀
      ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum)
    (x : ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).Raw P.B₀)
    (hx : (Quot.mk _ x :
      ((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).Pt P.B₀) = P.univ)

    (R₀ : Type) [CommRing R₀] [IsLocalRing R₀] [IsNoetherianRing R₀] [IsAdicComplete (maximalIdeal R₀) R₀]
    [Algebra A₀ R₀] (ι : P.B₀ →ₐ[A₀] R₀)
    (k : Type) [Field k] (hℓk : ((ℓ : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
    (resR : R₀ →+* k) (hresR : Function.Surjective resR) (hkerR : RingHom.ker resR = maximalIdeal R₀)

    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    [Algebra W₀ R₀] [Algebra A₀ W₀] [IsScalarTower A₀ W₀ R₀]
    (hresR₀ : ∀ w : W₀, resR (algebraMap W₀ R₀ w) = res₀ w)
    (hfac : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : P.B₀ →ₐ[A₀] T, (∀ b : P.B₀, resT (φ b) = resR (ι b)) →
          ∃! Φ : R₀ →ₐ[W₀] T, (∀ r : R₀, resT (Φ r) = resR r) ∧ ∀ b : P.B₀, Φ (ι b) = φ b) :
    Nonempty (R₀ ≃ₐ[W₀] PowerSeries W₀) := by sorry
