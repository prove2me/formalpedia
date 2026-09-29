-- Prove2me | Theorems.Thm_ModularCurve_exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff
-- name    : ModularCurve.exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/a3957ae1-b183-5a9b-88e9-cb42e33df0cc
-- title:
--   Diamond action on the function field of X₁(M) and Γ_H-invariants
-- statement:
--   Let $K$ be an algebraically closed field, let $M$ be a positive integer, and assume $M \neq 0$ in $K$. For a subgroup $H \le (\mathbb{Z}/M)^\times$ write $\Gamma_H(M) \le \mathrm{SL}_2(\mathbb{Z})$ for the image of the subgroup of $\Gamma_0(M)$ consisting of those $\gamma$ whose lower-right entry mod $M$ lies in $H$ (a unit of $\mathbb{Z}/M$, with inverse the upper-left entry mod $M$), so $\Gamma_\bot(M)$ is the case $H = \{1\}$; and write $F_\Gamma = K(\,\mathrm{intFormRatiosC}\,) \subseteq K((q))$ for the intermediate field `qExpFunctionFieldC K Γ` generated over $K$ by all quotients $\bar p_f/\bar p_g$, where $f,g$ are modular forms of one and the same weight $k$ on $\Gamma$ (viewed in $\mathrm{GL}_2(\mathbb{R})$), $p_f,p_g \in \mathbb{Z}[[q]]$ are integral power series whose complex images are the $q$-expansions of $f$ and $g$, the bar denoting coefficientwise reduction into $K((q))$, and $\bar p_g \neq 0$. The assertion is the existence of a monoid homomorphism $\rho$ from $\Gamma_0(M)$ to the group of $K$-algebra automorphisms of $F_{\Gamma_\bot(M)}$ with two properties. First, `IsDiamondPullbackModL K M ⊥ ρ`: for every $\gamma \in \Gamma_0(M)$, every weight $k$, all modular forms $f,g,f_1,g_1$ of weight $k$ on $\Gamma_\bot(M)$ with integral $q$-expansion power series $p_f,p_g,p_{f_1},p_{g_1}$ such that $f_1 = f\mid_k\gamma$ and $g_1 = g\mid_k\gamma$ as functions on the upper half-plane and $\bar p_g \neq 0$, every element $x$ of $F_{\Gamma_\bot(M)}$ whose Laurent series is $\bar p_{f_1}/\bar p_{g_1}$ satisfies $\rho(\gamma)x = \bar p_f/\bar p_g$. Secondly, the Galois correspondence: for every subgroup $H \le (\mathbb{Z}/M)^\times$ and every $y \in F_{\Gamma_\bot(M)}$, the Laurent series of $y$ lies in $F_{\Gamma_H(M)}$ if and only if $\rho(\gamma)y = y$ for all $\gamma \in \Gamma_0(M)$ whose image in $\mathrm{SL}_2(\mathbb{Z})$ lies in $\Gamma_H(M)$.
--
--   This identifies the diamond action of $\Gamma_0(M)/\Gamma_1(M) \cong (\mathbb{Z}/M)^\times$ on the function field over $K$ of the model of $X_1(M)$ in which the cusp at infinity is rational, characterised by the pull-back formula on ratios of $q$-expansions, together with the statement that the function field of $X_H(M)$ is exactly the field of $\Gamma_H(M)$-invariants. It is used in the construction of automorphisms of the function fields of the curves $X_H(M)$ and in the local analysis of $X_1(M) \to X_0(p)$ that computes inertia subgroups at the relevant points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDiamondModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
open scoped MatrixGroups

universe u in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_isDiamondPullbackModL_bot_forall_coe_mem_gammaH_iff
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    ∃ ρ : CongruenceSubgroup.Gamma0 M →*
        (qExpFunctionFieldC K (CohCarrier.GammaH M ⊥) ≃ₐ[K]
          qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)),
      IsDiamondPullbackModL K M ⊥ ρ ∧
      ∀ (H : Subgroup (ZMod M)ˣ) (y : qExpFunctionFieldC K (CohCarrier.GammaH M ⊥)),
        (y : LaurentSeries K) ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H) ↔
          ∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ y = y := by sorry
