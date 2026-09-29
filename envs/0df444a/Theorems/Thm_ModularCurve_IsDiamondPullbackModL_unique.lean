-- Prove2me | Theorems.Thm_ModularCurve_IsDiamondPullbackModL_unique
-- name    : ModularCurve.IsDiamondPullbackModL.unique
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/62359102-f8f7-5df3-a87e-d73de2db030f
-- title:
--   Uniqueness of a diamond pull-back action on ̄ F(Γ_H(M))
-- statement:
--   Let $K$ be a field, let $M$ be a nonzero natural number with $(M:K)\neq 0$, and let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$. Write $\Gamma_H(M)$ for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image under the inclusion $\Gamma_0(M)\hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(M)\to(\mathbb{Z}/M)^\times$ sending $\gamma$ to its lower-right entry modulo $M$, and write $\bar F=$ `qExpFunctionFieldC K (CohCarrier.GammaH M H)` for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by all quotients $\bar p_f/\bar p_g$, where $f,g$ are modular forms of a common weight $k$ on $\Gamma_H(M)$ (viewed in $\mathrm{GL}_2(\mathbb{R})$), $p_f,p_g\in\mathbb{Z}[[q]]$ are integral $q$-expansions of $f,g$ (i.e. their images in $\mathbb{C}[[q]]$ are the $q$-expansions of $f,g$), $\bar{\;}$ denotes coefficientwise reduction into $K((q))$, and $\bar p_g\neq 0$. Let $\rho,\rho'\colon\Gamma_0(M)\to \mathrm{Aut}_K(\bar F)$ be monoid homomorphisms into the group of $K$-algebra automorphisms of $\bar F$, each satisfying `IsDiamondPullbackModL`: for every $\gamma\in\Gamma_0(M)$, every weight $k$, all weight-$k$ forms $f,g,f_1,g_1$ on $\Gamma_H(M)$ with integral $q$-expansions $p_f,p_g,p_{f_1},p_{g_1}$ such that $f_1=f\mid_k\gamma$ and $g_1=g\mid_k\gamma$ as functions on the upper half plane and $\bar p_g\neq 0$, every $x\in\bar F$ whose underlying Laurent series is $\bar p_{f_1}/\bar p_{g_1}$ is sent by the automorphism at $\gamma$ to the element with underlying Laurent series $\bar p_f/\bar p_g$. Then $\rho=\rho'$.
--
--   This is the uniqueness half of the construction of the reduced diamond action of $\Gamma_0(M)$ on the $q$-expansion function field of $X_H(M)$ over $K$, the action given on modular functions by precomposition with $\gamma^{-1}$ and characterised by the pull-back formula on ratios of integral $q$-expansions. It is used to identify the diamond action in the compatibility statements [`ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul`](thm.html#ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul) and [`ModularCurve.qExpFrobeniusPushforwardModL_ofAlgAut_diamondActionModL_smul`](thm.html#ModularCurve.qExpFrobeniusPushforwardModL_ofAlgAut_diamondActionModL_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IsDiamondPullbackModL_unique.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDiamondModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.IsDiamondPullbackModL.unique
    (K : Type*) [Field K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) (H : Subgroup (ZMod M)ˣ)
    {ρ ρ' : CongruenceSubgroup.Gamma0 M →*
      (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))}
    (hρ : ModularCurve.IsDiamondPullbackModL K M H ρ)
    (hρ' : ModularCurve.IsDiamondPullbackModL K M H ρ') :
    ρ = ρ' := by sorry
