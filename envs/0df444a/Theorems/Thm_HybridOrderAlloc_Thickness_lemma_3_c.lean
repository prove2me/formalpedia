-- Prove2me | Theorems.Thm_HybridOrderAlloc_Thickness_lemma_3_c
-- name    : HybridOrderAlloc.Thickness.lemma_3_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:06.428775+00:00
-- url     : https://prove2.me/theorems/cadb4600-168c-47f5-8102-9ede8c85cea8
-- title:
--   Lemma 3(c), p. 37, with the added hypothesis µ₀ ≤ µ — then ∂₁V_s = G(s), ∂₂V_s = L(s) and y*_s = 0 for all s ≥ t
-- statement:
--   Consider the order-allocation dynamic program of He & Goh, the right partial derivatives $\partial_1V_s$, $\partial_2V_s$, the function $G$ of (17) and $L(s)=r\sum_{j=0}^{T-s}\gamma^j\eta^j$.
--
--   Assume $\mu_0\le\mu$, and suppose that for some period $t\in\{1,\dots,T\}$
--   $$(\mu_0-\mu)+\frac{\gamma\delta}{2p}\,G(t+1)<0.$$
--   Then for every period $s\in\{t,\dots,T\}$ and every $(M,D)\in\mathbb R^2_{++}$,
--   $$\partial_1V_s(M,D)=G(s),\qquad \partial_2V_s(M,D)=L(s),$$
--   and $y=0$ is the unique optimal decision of problem (5) in period $s$.
--
--   The lemma identifies the periods in which no orders are transferred to the platform, and there the marginal values are explicit; it yields the coincidence $\tau_1=\tau_2$ in Theorem 1(c).
--
--   **Correction** The hypothesis $\mu_0\le\mu$ is added to the page's statement, which is false for $\mu<\mu_0$: in the last period the optimal transfer is $(\mu_0-\mu)M\wedge D>0$, while the displayed hypothesis can still hold at $t=T-1$ when $G(T)=p\tilde\mu$ is very negative. The paper applies the lemma only when $\mu>\mu_0$.
--
--   **Formalization Note** All statements share the model `Sys` and its standing assumptions `Sys.Standing` (§3). Three kinds of hypotheses are added to the page and disclosed: $r \ge 0$ (Theorem 1 is false for $r<0$); $\rho + \delta R\beta > 0$, $\theta \ge 0$ and $\epsilon \ge 0$ almost surely, which keep the next state of (5) in the domain $M>0$, $D\ge 0$; and $T \ge 1$. Derivatives are right partial derivatives, as in the Notation paragraph of Appendix A.
-- source:
--   He & Goh, Profit or Growth? Dynamic Order Allocation in a Hybrid Workforce, SSRN 3537700 (preprint, 2020-12-25), p. 37, Lemma 3(c), corrected by the hypothesis µ₀ ≤ µ (the printed statement fails for µ < µ₀)

import Mathlib
import Definitions.Def_HybridOrderAlloc_Thickness_Model

namespace HybridOrderAlloc.Thickness

/-- **Lemma 3(c)**, p. 37, **corrected by the added hypothesis `µ₀ ≤ µ`**: as printed the lemma is
false for `µ < µ₀`, because then `y*_T = (µ₀ − µ)M ∧ D > 0`. If `µ₀ ≤ µ` and
`(µ₀ − µ) + (γδ/2p) G(t + 1) < 0` for some `t ∈ {1, …, T}`, then for every `s ∈ {t, …, T}` and
`(M, D) ∈ ℝ²₊₊`: `∂₁V_s(M, D) = G(s)`, `∂₂V_s(M, D) = L(s)`, and `y = 0` is the unique optimal
decision of (5) in period `s`.
Standing assumptions of §3, with the disclosed additions `r ≥ 0` and `ρ + δRβ > 0`,
`θ ≥ 0`, `ϵ ≥ 0` almost surely (well-posedness of (5)), and `T ≥ 1`. -/
theorem lemma_3_c {Ω : Type*} [MeasurableSpace Ω] (S : Sys Ω) (hS : S.Standing)
    (hmu : S.mu0 ≤ S.mu) :
    ∀ t : ℕ, 1 ≤ t → t ≤ S.T →
      (S.mu0 - S.mu) + S.gam * S.delta / (2 * S.p) * S.Gfun ((t : ℤ) + 1) < 0 →
      ∀ s : ℕ, t ≤ s → s ≤ S.T → ∀ M D : ℝ, 0 < M → 0 < D →
        S.d1V s M D = S.Gfun (s : ℤ) ∧ S.d2V s M D = S.Lfun s ∧
          IsMaxOn (S.stage (S.V (s + 1)) M D) (Set.Icc 0 D) 0 ∧
          ∀ y ∈ Set.Icc 0 D, IsMaxOn (S.stage (S.V (s + 1)) M D) (Set.Icc 0 D) y → y = 0 := by sorry

end HybridOrderAlloc.Thickness
