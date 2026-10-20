-- Prove2me | Theorems.Thm_HybridOrderAlloc_Thickness_lemma_2
-- name    : HybridOrderAlloc.Thickness.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:11.914154+00:00
-- url     : https://prove2.me/theorems/cc6f5e09-ed26-4b93-9cc8-0e74fbbf160c
-- title:
--   Lemma 2, p. 37 — K(t) = lim_{M→∞} ∂₁V_t exists independently of D, L(t) = lim_{M→0} ∂₂V_t, ∂₁V_t ≥ K(t), ∂₂V_t ≥ L(t)
-- statement:
--   Consider the order-allocation dynamic program of He & Goh, the right partial derivatives $\partial_1V_t$, $\partial_2V_t$ of the value function, and $L(t)=r\sum_{j=0}^{T-t}\gamma^j\eta^j$.
--
--   For every $t\in\{1,\dots,T+1\}$:
--   1. there is a constant $K(t)$, the same for every $D>0$, such that $\displaystyle K(t)=\lim_{M\to\infty}\partial_1V_t(M,D)$ for every $D>0$;
--   2. for every $D>0$, $\displaystyle L(t)=\lim_{M\to0^+}\partial_2V_t(M,D)$;
--   3. $\partial_1V_t(M,D)\ge K(t)$ and $\partial_2V_t(M,D)\ge L(t)$ for all $(M,D)\in\mathbb R^2_{++}$.
--
--   $K(t)$ is the asymptotic marginal value of thickness, whose sign decides whether thickness is eventually costly (Theorem 1(c)).
--
--   **Formalization Note** All statements share the model `Sys` and its standing assumptions `Sys.Standing` (§3). Three kinds of hypotheses are added to the page and disclosed: $r \ge 0$ (Theorem 1 is false for $r<0$); $\rho + \delta R\beta > 0$, $\theta \ge 0$ and $\epsilon \ge 0$ almost surely, which keep the next state of (5) in the domain $M>0$, $D\ge 0$; and $T \ge 1$. Derivatives are right partial derivatives, as in the Notation paragraph of Appendix A.
-- source:
--   He & Goh, Profit or Growth? Dynamic Order Allocation in a Hybrid Workforce, SSRN 3537700 (preprint, 2020-12-25), p. 37, Lemma 2(a)–(c)

import Mathlib
import Definitions.Def_HybridOrderAlloc_Thickness_Model

namespace HybridOrderAlloc.Thickness

open Filter Topology

/-- **Lemma 2**, p. 37: for every `t ∈ {1, …, T + 1}`:
(a) and the first half of (c): there is a constant `K(t)`, the same for every `D > 0`, with
`∂₁V_t(M, D) → K(t)` as `M → ∞`, and `∂₁V_t ≥ K(t)` on `ℝ²₊₊`;
(b) `∂₂V_t(M, D) → L(t) = r Σ_{j=0}^{T−t} γ^j η^j` as `M → 0⁺`, for every `D > 0`;
the second half of (c): `∂₂V_t ≥ L(t)` on `ℝ²₊₊`.
Standing assumptions of §3, with the disclosed additions `r ≥ 0` and `ρ + δRβ > 0`,
`θ ≥ 0`, `ϵ ≥ 0` almost surely (well-posedness of (5)), and `T ≥ 1`. -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] (S : Sys Ω) (hS : S.Standing) :
    ∀ t : ℕ, 1 ≤ t → t ≤ S.T + 1 →
      (∃ K : ℝ, (∀ D : ℝ, 0 < D → Tendsto (fun M => S.d1V t M D) atTop (𝓝 K)) ∧
          ∀ M D : ℝ, 0 < M → 0 < D → K ≤ S.d1V t M D) ∧
        (∀ D : ℝ, 0 < D → Tendsto (fun M => S.d2V t M D) (𝓝[>] 0) (𝓝 (S.Lfun t))) ∧
        (∀ M D : ℝ, 0 < M → 0 < D → S.Lfun t ≤ S.d2V t M D) := by sorry

end HybridOrderAlloc.Thickness
