-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_trivial_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_trivial_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/b7899993-285c-5b71-805f-d8ad1d9c41a0
-- title:
--   Infinitesimal lifting for the H₁ rigid Weierstrass moduli problem
-- statement:
--   Fix a prime $\ell$ with $\ell \ge 5$, a natural number $M' \neq 0$ and a commutative ring $A_0$, together with three variable-change compatibility hypotheses, stated for all $A_0$-algebras $T$, all Weierstrass curves $W/T$ and all $C \in \mathrm{VariableChange}(T)$: (hℓ) if $D = (x_P,y_P,x_Q,y_Q)$ is a $\Gamma_1(\ell)$-point of $W$ (i.e. $(x_P,y_P)$ satisfies the affine equation, $(\mathrm{pre}\Psi_\ell)(x_P)=0$, and $x_Q=x_P$, $y_Q=y_P$), then its translate $D \cdot C$ is one for $C \bullet W$; (hM) `IsGamma0PowAt W p k h` — which is `IsTwoKernel` when $p^k=2$ and otherwise the cyclic generator-kernel condition on $h$ — is preserved by $h \mapsto$ `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; (hL) divisibility $h \mid$ `inLineMulPoly W ℓ n x` is preserved by the same substitution, with $x$ replaced by $u^{-2}(x-r)$. Let $\pi : B \to T$ be a surjective $A_0$-algebra homomorphism whose kernel satisfies $(\ker \pi)^n = 0$ for some $n$, and assume $\ell$ and $M'$ are units in $T$. Then the map induced by $\pi$ on points of the associated moduli datum is surjective; a point over a ring is a variable-change equivalence class of a Weierstrass curve $W$ with $\Delta$ a unit, a family $h_p$ of polynomials indexed by the prime factors $p \mid M'$ with `IsGamma0PowAt W p (M'.factorization p) (h p)`, a $\Gamma_1(\ell)$-point $D$, a trivial third entry, and the link condition: if $\ell \mid M'$ then $h_\ell$ divides `inLineMulPoly W ℓ (ℓ ^ (M'.factorization ℓ - 1)) D.xP`.
--
--   This is the formal-smoothness (infinitesimal lifting) half of the assertion that the rigidified Weierstrass moduli problem of level $H_1 = \Gamma_0(M') \cap \Gamma_1(\ell)$ is smooth over $A_0$-algebras in which $\ell M'$ is invertible. It is used in the passage from this moduli problem to power-series rings, namely by [`ModularCurve.LevelModuliPackageAbs.nonempty_algEquiv_powerSeries_of_factorsThrough_trivial_rigidDataH1Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.nonempty_algEquiv_powerSeries_of_factorsThrough_trivial_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_trivial_rigidDataH1Pow.lean

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

theorem ModularCurve.FullLevel.Diamond.map_surjective_of_surjective_of_ker_pow_eq_bot_of_isUnit_trivial_rigidDataH1Pow
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
    {B T : Type} [CommRing B] [CommRing T] [Algebra A₀ B] [Algebra A₀ T]
    (π : B →ₐ[A₀] T) (hπ : Function.Surjective π) (hnil : ∃ n : ℕ, RingHom.ker π.toRingHom ^ n = ⊥)
    (hℓT : IsUnit ((ℓ : ℕ) : T)) (hM'T : IsUnit ((M' : ℕ) : T)) :
    Function.Surjective (((((ModularCurve.gamma0PowComponent A₀ M' hM).prod
        ((ModularCurve.gamma1Component A₀ ℓ hℓ).prod (ModularCurve.LevelComponent.trivial (A := A₀)))).restrict
        (fun W x => ModularCurve.IsGamma1Link W ℓ M' x.1 x.2.1)
        (fun f _ _ _ hx => ModularCurve.IsGamma1Link.map f.toRingHom hx)
        (fun C W _ _ hx => fun hmem => hL _ W C _ _ _ _ (hx hmem))).toRigid).toLevelModuliDatum.map π) := by sorry
