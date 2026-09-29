-- Prove2me | Theorems.Thm_ModularCurve_IsDiamondPullbackModL_apply_eq_self_of_coe_mem_qExpFunctionFieldC_gamma0
-- name    : ModularCurve.IsDiamondPullbackModL.apply_eq_self_of_coe_mem_qExpFunctionFieldC_gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/100b989d-113f-5af5-a1f9-8f4c442c7f8d
-- title:
--   Diamond pullback action fixes the Γ₀(N) q-expansion field
-- statement:
--   Let $K$ be a field and $N$ a nonzero natural number, and let $H'$ be a subgroup of $(\mathbb{Z}/N)^\times$. Write $\Gamma_{H'} =$ [`CohCarrier.GammaH N H'`](def/CohCarrier_Level.html#L133) for the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image under the inclusion $\Gamma_0(N)\hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H'$ under the character sending $\gamma \in \Gamma_0(N)$ to its lower-right entry modulo $N$, and for a subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb{Z})$ write $F_K(\Gamma) =$ [`ModularCurve.qExpFunctionFieldC K Γ`](def/ModularCurve_X1.html#L101) for the intermediate field of $K((q))$ generated over $K$ by all ratios $\bar p_f/\bar p_g$, where $f,g$ are modular forms of some common weight $k$ on the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$ with integral $q$-expansions $p_f, p_g \in \mathbb{Z}[[q]]$ (that is, $p_f$, $p_g$ push forward to the complex $q$-expansions of $f$, $g$), $\bar{\;}$ denoting the image in $K((q))$ and $\bar p_g \neq 0$. Let $\rho$ be a homomorphism from $\Gamma_0(N)$ to the group of $K$-algebra automorphisms of $F_K(\Gamma_{H'})$ satisfying [`ModularCurve.IsDiamondPullbackModL`](def/ModularCurve_XHDiamondModL.html#L12): for all $\gamma$, all weights $k$, all forms $f,g,f_1,g_1$ of weight $k$ on $\Gamma_{H'}$ with integral $q$-expansions $p_f,p_g,p_{f_1},p_{g_1}$ such that $f_1 = f\mid_k \gamma$ and $g_1 = g\mid_k \gamma$ as functions on the upper half-plane and $\bar p_g \neq 0$, every $x \in F_K(\Gamma_{H'})$ with Laurent series $\bar p_{f_1}/\bar p_{g_1}$ satisfies $\rho(\gamma)x = \bar p_f/\bar p_g$. Then for every $\gamma \in \Gamma_0(N)$ and every $x \in F_K(\Gamma_{H'})$ whose underlying Laurent series lies in $F_K(\Gamma_0(N))$, one has $\rho(\gamma)x = x$.
--
--   This records that any action of $\Gamma_0(N)$ on the $q$-expansion function field of $\Gamma_{H'}(N)$ normalised by the diamond pullback formula restricts to the identity on the subfield of $q$-expansions coming from level $\Gamma_0(N)$ — the function-field counterpart of the fact that the diamond operators act trivially on $X_0(N)$. It is used in the analysis of places and Frobenius data on the $q$-expansion field, in particular in the comparison of the diamond action with the specialisation and Frobenius places attached to level $\Gamma_{H'}(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsDiamondPullbackModL_apply_eq_self_of_coe_mem_qExpFunctionFieldC_gamma0.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.IsDiamondPullbackModL.apply_eq_self_of_coe_mem_qExpFunctionFieldC_gamma0
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    {ρ : CongruenceSubgroup.Gamma0 N →*
        (↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')) ≃ₐ[K] ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')))}
    (hρ : ModularCurve.IsDiamondPullbackModL K N H' ρ)
    (γ : CongruenceSubgroup.Gamma0 N) (x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')))
    (hx : (x : LaurentSeries K) ∈ ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 N)) :
    ρ γ x = x := by sorry
