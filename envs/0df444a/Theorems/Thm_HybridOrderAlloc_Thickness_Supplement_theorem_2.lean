-- Prove2me | Theorems.Thm_HybridOrderAlloc_Thickness_Supplement_theorem_2
-- name    : HybridOrderAlloc.Thickness.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:08:54.871192+00:00
-- url     : https://prove2.me/theorems/93b6b11f-e5c1-4050-9cbc-0636f0071c23
-- title:
--   Theorem 2, p. 21 — the optimal dynamic transfer is at most the static one on R1 and at least it on R2, in every period and state
-- statement:
--   Consider the firm–platform order-allocation dynamic program (5) of He and Goh over periods $t\in\{1,\dots,T\}$, with value functions $V_t(M,D)$ and $V_{T+1}=0$. In period $t$ at state $(M,D)$, $M>0$ the market thickness and $D>0$ the firm demand, the firm chooses how many orders $y\in[0,D]$ to transfer to the platform, maximizing
--
--   $$r(D-y)+\mathbb E\Big[p(y+\beta M)\Big(1-\frac{R(y+\beta M)}{M}\Big)\Big]+\gamma\,\mathbb E\,V_{t+1}\big((\rho+\delta R\beta)M+\delta Ry,\ \eta D+\theta M+\epsilon\big).$$
--
--   An **optimal dynamic decision** $y^*_t(M,D)$ is any maximizer of this objective over $[0,D]$. Let $\mu=\mathbb E\beta$, $\sigma^2=\operatorname{Var}\beta$, $\mu_0=(p-r)/(2pR)$, let $\mathcal R_1$ (high variance) and $\mathcal R_2$ (low variance) be the parametric regions of Definition 1, (6), and let $y^{\mathrm{static}}(M,D)=\min\{(\mu_0-\mu)_+M,\,D\}$ be the static policy of §4.3.
--
--   **Theorem 2.** For every period $t\in\{1,\dots,T\}$, every state $(M,D)$ with $M,D>0$, and every optimal dynamic decision $y^*_t(M,D)$:
--
--   1. if $(\mu,\sigma)\in\mathcal R_1$, then $$y^*_t(M,D)\le y^{\mathrm{static}}(M,D);$$
--   2. if $(\mu,\sigma)\in\mathcal R_2$, then $$y^*_t(M,D)\ge y^{\mathrm{static}}(M,D).$$
--
--   In the high-variance regime, where market thickness is costly (Theorem 1(a)), the dynamic firm sends fewer orders to its platform than a myopic firm would; in the low-variance regime, where thickness pays off (Theorem 1(b)), it sends more, to grow the platform. In the final period $T$ both policies coincide.
--
--   **Formalization Note** The statement uses the published model `HybridOrderAlloc.Thickness.Model`: its standing assumptions, the objective `stage`, the value functions `V`, and the region predicates `InR1` (which requires $\gamma\eta<1$, since $\mathcal R_1$ is empty when $\Delta=+\infty$) and `InR2`. The theorem is stated for every maximizer $y$; by Lemma 1(c) a maximizer exists, and it is unique because the objective is strictly concave in $y$.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §3 → the published `Sys.Standing`, including the base mission's disclosed additions r ≥ 0, T ≥ 1 and ρ + δRβ > 0, θ ≥ 0, ϵ ≥ 0 almost surely; reason: inherited unchanged from the published model; the proof of Theorem 2 (p. 40) uses Theorem 1(a)–(b), which is stated under these hypotheses and is false for r < 0
--   - reading: the optimal dynamic policy y∗t(M, D) → every y ∈ [0, D] that maximizes the objective of (5) with continuation V_{t+1}; reason: the optimal decision is unique (strictly concave term −pRy²/M plus a continuation concave in y by Proposition 1), and its existence is Lemma 1(c), so the claim for every maximizer is the paper's claim
--   - reading: for each state (M, D) and every period t ∈ T → for all M > 0, D > 0 and 1 ≤ t ≤ T; reason: the state space of (5) is R²₊₊ and T = {1, …, T}
-- source:
--   He & Goh, Profit or Growth? Dynamic Order Allocation in a Hybrid Workforce, SSRN 3537700 (preprint, 2020-12-25), p. 21, Theorem 2 (proof p. 40)

import Mathlib
import Definitions.Def_HybridOrderAlloc_Thickness_Model
import Definitions.Def_HybridOrderAlloc_Thickness_Supplement_StaticPolicy

namespace HybridOrderAlloc.Thickness.Supplement

/-- **Theorem 2**, p. 21 (He & Goh, SSRN 3537700). For every period `t ∈ {1, …, T}`, every state
`(M, D)` with `M > 0`, `D > 0`, and every optimal decision `y` of (5) in period `t` at `(M, D)`
(a maximizer over `0 ≤ y ≤ D` of the objective of (5) with continuation `V_{t+1}`):
(a) in `R₁`, `y ≤ y^static(M, D)`; (b) in `R₂`, `y ≥ y^static(M, D)`.
Standing assumptions of §3, with the base mission's disclosed additions `r ≥ 0`, `T ≥ 1` and
`ρ + δRβ > 0`, `θ ≥ 0`, `ϵ ≥ 0` almost surely. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (S : Sys Ω) (hS : S.Standing) :
    ∀ t : ℕ, 1 ≤ t → t ≤ S.T → ∀ M D : ℝ, 0 < M → 0 < D →
      ∀ y : ℝ, y ∈ Set.Icc 0 D → IsMaxOn (S.stage (S.V (t + 1)) M D) (Set.Icc 0 D) y →
        (S.InR1 → y ≤ yStatic S M D) ∧ (S.InR2 → yStatic S M D ≤ y) := by sorry

end HybridOrderAlloc.Thickness.Supplement
