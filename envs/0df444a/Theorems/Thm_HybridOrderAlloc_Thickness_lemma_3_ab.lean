-- Prove2me | Theorems.Thm_HybridOrderAlloc_Thickness_lemma_3_ab
-- name    : HybridOrderAlloc.Thickness.lemma_3_ab
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:11.918078+00:00
-- url     : https://prove2.me/theorems/91a98b50-c524-4c05-b4b8-b88166ac24a0
-- title:
--   Lemma 3(a)–(b), p. 37 — K(t) ≥ G(t) with G of (17), and G(t) ≥ G(t+1) propagates backwards
-- statement:
--   Consider the order-allocation dynamic program of He & Goh, the right partial derivative $\partial_1V_t$ of the value function in $M$, and the explicit function, for integers $t\le T+1$,
--   $$G(t)=\sum_{i=0}^{T-t}\gamma^i(\rho+\delta R\mu)^i\Big(p\tilde\mu+\gamma r\mu_\theta\sum_{j=0}^{T-t-1-i}\gamma^j\eta^j\Big).\qquad(17)$$
--
--   1. For every $t\in\{1,\dots,T+1\}$, the limit $K(t)=\lim_{M\to\infty}\partial_1V_t(M,D)$ exists, is the same for every $D>0$, and $K(t)\ge G(t)$.
--   2. For integers $t\le T$: if $G(t)\ge G(t+1)$, then $G(s)\ge G(s+1)$ for every integer $s\le t$.
--
--   $G$ is an explicit lower bound for the asymptotic marginal value of thickness; part 2 says $G$ can change from increasing to decreasing at most once going backwards in time, which produces the threshold periods of Theorem 1(c).
--
--   **Formalization Note (part 2)** Part 2 is stated for $t\le T$, so that $G(t+1)$ lies in the domain $t\le T+1$ of (17).
--
--   **Formalization Note** All statements share the model `Sys` and its standing assumptions `Sys.Standing` (§3). Three kinds of hypotheses are added to the page and disclosed: $r \ge 0$ (Theorem 1 is false for $r<0$); $\rho + \delta R\beta > 0$, $\theta \ge 0$ and $\epsilon \ge 0$ almost surely, which keep the next state of (5) in the domain $M>0$, $D\ge 0$; and $T \ge 1$. Derivatives are right partial derivatives, as in the Notation paragraph of Appendix A.
-- source:
--   He & Goh, Profit or Growth? Dynamic Order Allocation in a Hybrid Workforce, SSRN 3537700 (preprint, 2020-12-25), p. 37, Lemma 3(a)–(b), (17)

import Mathlib
import Definitions.Def_HybridOrderAlloc_Thickness_Model

namespace HybridOrderAlloc.Thickness

open Filter Topology

/-- **Lemma 3(a)–(b)**, p. 37, with `G` of (17).
(a) For every `t ∈ {1, …, T + 1}`, `K(t) = lim_{M→∞} ∂₁V_t(M, D)` exists, is the same for every
`D > 0`, and `K(t) ≥ G(t)`.
(b) For integers `t ≤ T`: if `G(t) ≥ G(t + 1)`, then `G(s) ≥ G(s + 1)` for every integer `s ≤ t`
(restricted to `t ≤ T`, where `G(t + 1)` lies in the domain `t ≤ T + 1` of (17)).
Standing assumptions of §3, with the disclosed additions `r ≥ 0` and `ρ + δRβ > 0`,
`θ ≥ 0`, `ϵ ≥ 0` almost surely (well-posedness of (5)), and `T ≥ 1`. -/
theorem lemma_3_ab {Ω : Type*} [MeasurableSpace Ω] (S : Sys Ω) (hS : S.Standing) :
    (∀ t : ℕ, 1 ≤ t → t ≤ S.T + 1 →
      ∃ K : ℝ, (∀ D : ℝ, 0 < D → Tendsto (fun M => S.d1V t M D) atTop (𝓝 K)) ∧
        S.Gfun t ≤ K) ∧
    (∀ t : ℤ, t ≤ S.T → S.Gfun (t + 1) ≤ S.Gfun t →
      ∀ s : ℤ, s ≤ t → S.Gfun (s + 1) ≤ S.Gfun s) := by sorry

end HybridOrderAlloc.Thickness
