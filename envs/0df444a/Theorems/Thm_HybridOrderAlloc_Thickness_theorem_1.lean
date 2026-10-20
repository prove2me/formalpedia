-- Prove2me | Theorems.Thm_HybridOrderAlloc_Thickness_theorem_1
-- name    : HybridOrderAlloc.Thickness.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:22.097839+00:00
-- url     : https://prove2.me/theorems/2de97193-280f-4b21-8f9c-887f082ba932
-- title:
--   Theorem 1, p. 15, with r ≥ 0 and a.s. well-posed transitions — thickness is costly on R1, beneficial on R2, and switches at τ₁ ≤ τ₂ on R3
-- statement:
--   Consider the order-allocation dynamic program of He & Goh: value functions $V_t(M,D)$ of market thickness $M$ and firm demand $D$ given by (5), the mean $\mu$ and variance $\sigma^2$ of the cross-network effect, $\mu_0=(p-r)/(2pR)$, and the regions $\mathcal R_1,\mathcal R_2,\mathcal R_3$ of (6). Market thickness *benefits* the system in period $t$ if $V_t(M,D)$ is increasing in $M$ for every fixed $D>0$, and *is costly* if it is decreasing (both in the weak sense).
--
--   The relationship between the system and market thickness differs across the three regions:
--   1. if $(\mu,\sigma)\in\mathcal R_1$ (high variance), market thickness is costly to the system in every period $t\in\{1,\dots,T\}$;
--   2. if $(\mu,\sigma)\in\mathcal R_2$ (low variance), market thickness benefits the system in every period;
--   3. if $(\mu,\sigma)\in\mathcal R_3$ (moderate variance), there are threshold periods $\tau_1,\tau_2\in\{1,\dots,T\}$ with $\tau_1\le\tau_2$ such that market thickness benefits the system in every period $t<\tau_1$, and is costly to the system in the limit as $M\to\infty$ in every period $t\ge\tau_2$; moreover, if $\mu>\mu_0$, then $\tau_1=\tau_2$.
--
--   "Costly in the limit as $M\to\infty$" means: for every $D>0$ there is $M_0>0$ such that $V_t(\cdot,D)$ is decreasing on $[M_0,\infty)$.
--
--   The theorem is the paper's headline result: the variance of the cross-network effect, not only its mean, decides whether growing the freelancer pool pays.
--
--   **Added hypothesis** The page assumes only $r<p$; the theorem is false for $r<0$ (with $\mu_\theta>0$, $\Delta<0$ and $\mathcal R_1$ meets points where $V_1$ is increasing in $M$), so $r\ge0$ is added.
--
--   **Formalization Note** All statements share the model `Sys` and its standing assumptions `Sys.Standing` (§3). Three kinds of hypotheses are added to the page and disclosed: $r \ge 0$ (Theorem 1 is false for $r<0$); $\rho + \delta R\beta > 0$, $\theta \ge 0$ and $\epsilon \ge 0$ almost surely, which keep the next state of (5) in the domain $M>0$, $D\ge 0$; and $T \ge 1$. Derivatives are right partial derivatives, as in the Notation paragraph of Appendix A.
-- source:
--   He & Goh, Profit or Growth? Dynamic Order Allocation in a Hybrid Workforce, SSRN 3537700 (preprint, 2020-12-25), p. 15, Theorem 1 (regions (6) of Definition 1)

import Mathlib
import Definitions.Def_HybridOrderAlloc_Thickness_Model

namespace HybridOrderAlloc.Thickness

/-- **Theorem 1**, p. 15 (He & Goh, SSRN 3537700).
(a) On `R₁`, market thickness is costly to the system in every period `t ∈ {1, …, T}`.
(b) On `R₂`, market thickness benefits the system in every period.
(c) On `R₃`, there are periods `1 ≤ τ₁ ≤ τ₂ ≤ T` such that thickness benefits the system in every
period `t < τ₁` and is costly to the system in the limit as `M → ∞` in every period `t ≥ τ₂`;
if `µ > µ₀`, then `τ₁ = τ₂`.
Standing assumptions of §3, with the disclosed additions `r ≥ 0` and `ρ + δRβ > 0`,
`θ ≥ 0`, `ϵ ≥ 0` almost surely (well-posedness of (5)), and `T ≥ 1`. The theorem is false as printed when `r < 0`. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (S : Sys Ω) (hS : S.Standing) :
    (S.InR1 → ∀ t : ℕ, 1 ≤ t → t ≤ S.T → S.Costly t) ∧
    (S.InR2 → ∀ t : ℕ, 1 ≤ t → t ≤ S.T → S.Benefits t) ∧
    (S.InR3 → ∃ τ₁ τ₂ : ℕ, 1 ≤ τ₁ ∧ τ₁ ≤ τ₂ ∧ τ₂ ≤ S.T ∧
      (∀ t : ℕ, 1 ≤ t → t < τ₁ → S.Benefits t) ∧
      (∀ t : ℕ, τ₂ ≤ t → t ≤ S.T → S.CostlyInLimit t) ∧
      (S.mu0 < S.mu → τ₁ = τ₂)) := by sorry

end HybridOrderAlloc.Thickness
