-- Prove2me | Theorems.Thm_HybridOrderAlloc_Thickness_lemma_1_d
-- name    : HybridOrderAlloc.Thickness.lemma_1_d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:06.111118+00:00
-- url     : https://prove2.me/theorems/e4025b3c-de8b-4f54-880e-4ea9cf12b3f2
-- title:
--   Lemma 1(d), p. 36 — bounds A ≤ ∂₁V_{t+1} ≤ B give the bounds (15) on y^U_t
-- statement:
--   Consider the order-allocation dynamic program of He & Goh, the right partial derivative $\partial_1V_{t+1}$ of $V_{t+1}$ in $M$, and the threshold $y^U_t$ of (14).
--
--   Let $t\in\{1,\dots,T\}$ and let $A,B\in\mathbb R$ satisfy $A\le\partial_1V_{t+1}(M,D)\le B$ for all $(M,D)\in\mathbb R^2_{++}$. Then for all $(M,D)\in\mathbb R^2_{++}$,
--   $$\Big(\mu_0-\mu+\frac{\gamma\delta A}{2p}\Big)_+M\ \le\ y^U_t(M,D)\ \le\ \Big(\mu_0-\mu+\frac{\gamma\delta B}{2p}\Big)_+M,\qquad(15)$$
--   where $x_+=\max\{x,0\}$.
--
--   The lemma turns bounds on the marginal value of thickness into linear bounds on the optimal transfer, and is the tool used to show that the optimal transfer vanishes in the regimes of Theorem 1.
--
--   **Formalization Note** All statements share the model `Sys` and its standing assumptions `Sys.Standing` (§3). Three kinds of hypotheses are added to the page and disclosed: $r \ge 0$ (Theorem 1 is false for $r<0$); $\rho + \delta R\beta > 0$, $\theta \ge 0$ and $\epsilon \ge 0$ almost surely, which keep the next state of (5) in the domain $M>0$, $D\ge 0$; and $T \ge 1$. Derivatives are right partial derivatives, as in the Notation paragraph of Appendix A.
-- source:
--   He & Goh, Profit or Growth? Dynamic Order Allocation in a Hybrid Workforce, SSRN 3537700 (preprint, 2020-12-25), p. 36, Lemma 1(d), (15)

import Mathlib
import Definitions.Def_HybridOrderAlloc_Thickness_Model

namespace HybridOrderAlloc.Thickness

/-- **Lemma 1(d)**, p. 36, (15): for every period `t ∈ {1, …, T}`, if `A ≤ ∂₁V_{t+1}(M, D) ≤ B` on
`ℝ²₊₊`, then `(µ₀ − µ + γδA/2p)₊ M ≤ y^U_t(M, D) ≤ (µ₀ − µ + γδB/2p)₊ M` on `ℝ²₊₊`.
Standing assumptions of §3, with the disclosed additions `r ≥ 0` and `ρ + δRβ > 0`,
`θ ≥ 0`, `ϵ ≥ 0` almost surely (well-posedness of (5)), and `T ≥ 1`. -/
theorem lemma_1_d {Ω : Type*} [MeasurableSpace Ω] (S : Sys Ω) (hS : S.Standing) :
    ∀ t : ℕ, 1 ≤ t → t ≤ S.T → ∀ A B : ℝ,
      (∀ M D : ℝ, 0 < M → 0 < D → A ≤ S.d1V (t + 1) M D ∧ S.d1V (t + 1) M D ≤ B) →
      ∀ M D : ℝ, 0 < M → 0 < D →
        max (S.mu0 - S.mu + S.gam * S.delta * A / (2 * S.p)) 0 * M ≤ S.yU t M D ∧
          S.yU t M D ≤ max (S.mu0 - S.mu + S.gam * S.delta * B / (2 * S.p)) 0 * M := by sorry

end HybridOrderAlloc.Thickness
