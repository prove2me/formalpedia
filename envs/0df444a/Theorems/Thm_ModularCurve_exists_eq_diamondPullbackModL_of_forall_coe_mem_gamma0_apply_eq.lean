-- Prove2me | Theorems.Thm_ModularCurve_exists_eq_diamondPullbackModL_of_forall_coe_mem_gamma0_apply_eq
-- name    : ModularCurve.exists_eq_diamondPullbackModL_of_forall_coe_mem_gamma0_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/d040e574-3359-5042-b7c5-538c52a8e4a7
-- title:
--   Automorphisms fixing the X₀(M) function field are diamonds
-- statement:
--   Let $K$ be an algebraically closed field and $M$ a nonzero natural number with $(M:K)\neq 0$. For a subgroup $H\le(\mathbb{Z}/M)^\times$ write $\Gamma_H(M)$ for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}_2(\mathbb{Z})$ of the set of $\gamma\in\Gamma_0(M)$ whose lower-right entry reduces into $H$, and write $F_H$ for `qExpFunctionFieldC K (CohCarrier.GammaH M H)`, the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the quotients $p_f/p_g$ of images in $K((q))$ of integral power series $p_f,p_g$ that are the $q$-expansions of weight-$k$ modular forms on $\Gamma_H(M)$, with $p_g\neq 0$. Given a homomorphism $\rho$ from $\Gamma_0(M)$ to the group of $K$-algebra automorphisms of $F_\bot$ satisfying `IsDiamondPullbackModL` (for $f_1=f\mid_k\gamma$, $g_1=g\mid_k\gamma$, the element $\rho(\gamma)$ carries $p_{f_1}/p_{g_1}$ to $p_f/p_g$), and assuming the Galois correspondence that for every $H$ and every $y\in F_\bot$ one has $y\in F_H$ precisely when $\rho(\gamma)y=y$ for all $\gamma\in\Gamma_0(M)$ with image in $\Gamma_H(M)$: any $K$-algebra automorphism $\sigma$ of $F_\bot$ fixing every element of $F_\top$ pointwise is of the form $\sigma=\rho(\gamma)$ for some $\gamma\in\Gamma_0(M)$. The proof uses neither the hypothesis $(M:K)\neq 0$ nor the hypothesis `IsDiamondPullbackModL`.
--
--   This is the statement that the automorphism group of the function field of $X_1(M)$ over that of $X_0(M)$ is exactly the group of diamond operators. It is used in the analysis of inertia at supersingular points on the two-chart integral model of $X_1(M)\cap X_0(p)$, where an abstract covering automorphism must be recognised as a diamond with a well-defined scalar in $(\mathbb{Z}/M)^\times$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_eq_diamondPullbackModL_of_forall_coe_mem_gamma0_apply_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDiamondModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups
universe u in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_eq_diamondPullbackModL_of_forall_coe_mem_gamma0_apply_eq
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (ρ : CongruenceSubgroup.Gamma0 M →*
        (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
          qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)))
    (hρ : IsDiamondPullbackModL K M ⊥ ρ)
    (hfix : ∀ (H : Subgroup (ZMod M)ˣ) (y : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)),
        (y : LaurentSeries K) ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H) ↔
          ∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ y = y)
    (σ : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH M ⊥))
    (hσ : ∀ y : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥),
        (y : LaurentSeries K) ∈ qExpFunctionFieldC K (CohCarrier.GammaH M ⊤) → σ y = y) :
    ∃ γ : CongruenceSubgroup.Gamma0 M, σ = ρ γ := by sorry
