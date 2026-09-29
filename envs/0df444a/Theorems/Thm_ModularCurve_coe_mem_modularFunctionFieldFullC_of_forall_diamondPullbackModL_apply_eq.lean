-- Prove2me | Theorems.Thm_ModularCurve_coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq
-- name    : ModularCurve.coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/ba805ab2-f9be-5f19-9fe2-9a16d3180475
-- title:
--   Diamond-invariant functions mod ℓ lie in level Γ₀(M)
-- statement:
--   Fix $M\ge 1$ and a subgroup $H\le(\mathbb{Z}/M)^\times$, a prime $\ell$ with $\ell\nmid M$, and an algebraically closed field $K$ of characteristic $\ell$. Write $\Gamma_H(M)$ for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the subgroup of $SL_2(\mathbb{Z})$ obtained as the image of those $\gamma\in\Gamma_0(M)$ whose associated unit [`CohCarrier.gamma0Units M γ`](def/CohCarrier_Level.html#L121) (the reduction mod $M$ of the lower-right entry) lies in $H$, and let $\bar F=$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)`](def/ModularCurve_X1.html#L101), the subfield of $K((q))$ generated over $K$ by all quotients $\mathrm{intSeriesC}\,K\,p_f/\mathrm{intSeriesC}\,K\,p_g$, where $f,g$ are modular forms of a common weight $k$ on $\Gamma_H(M)$, $p_f,p_g$ are integral power series whose images in $\mathbb{C}[[q]]$ are the $q$-expansions of $f,g$, and the coefficientwise reduction of $p_g$ in $K((q))$ is nonzero. Let $F_0=$ [`ModularCurve.modularFunctionFieldFullC K M`](def/ModularCurve_X0ModL.html#L100) be the subfield of $K((q))$ generated over $K$ by the series $\mathrm{qExpand}\,K\,d\,(\mathrm{jqModC}\,K)$ for the nonzero divisors $d\mid M$. Let $\rho$ be a homomorphism from $\Gamma_0(M)$ to the group of $K$-algebra automorphisms of $\bar F$ satisfying [`ModularCurve.IsDiamondPullbackModL`](def/ModularCurve_XHDiamondModL.html#L12): for all $\gamma\in\Gamma_0(M)$, all weight-$k$ forms $f,g,f_1,g_1$ on $\Gamma_H(M)$ with integral expansions $p_f,p_g,p_{f_1},p_{g_1}$ such that $f_1=f\mid_k\gamma$ and $g_1=g\mid_k\gamma$ as functions on $\mathbb{H}$ and the reduction of $p_g$ is nonzero, any $x\in\bar F$ with underlying series $\bar p_{f_1}/\bar p_{g_1}$ satisfies $\rho(\gamma)x=\bar p_f/\bar p_g$. Assume moreover that each $\rho(\gamma)$ fixes every $x\in\bar F$ whose Laurent series lies in $F_0$. Then every $u\in\bar F$ with $\rho(\gamma)u=u$ for all $\gamma\in\Gamma_0(M)$ has its Laurent series in $F_0$.
--
--   This is the characteristic-$\ell$ form, for $\ell\nmid M$, of the classical fact that the functions on $X_H(M)$ invariant under the diamond operators are exactly the functions on $X_0(M)$, i.e. that the covering $X_H(M)\to X_0(M)$ remains Galois with group a quotient of $(\mathbb{Z}/M)^\times/\langle H,-1\rangle$ after reduction. It is used in the comparison of fibres of the $j$-map with double cosets and in the construction of injections from double cosets into places of the reduced function field of $X_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_XHDiamondModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularCurve.coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (ρ : CongruenceSubgroup.Gamma0 M →*
      (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)))
    (hρ : ModularCurve.IsDiamondPullbackModL K M H ρ)
    (hfix : ∀ (γ : CongruenceSubgroup.Gamma0 M)
      (x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
      (x : LaurentSeries K) ∈ ModularCurve.modularFunctionFieldFullC K M → ρ γ x = x)
    (u : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hu : ∀ γ : CongruenceSubgroup.Gamma0 M, ρ γ u = u) :
    (u : LaurentSeries K) ∈ ModularCurve.modularFunctionFieldFullC K M := by sorry
