-- Prove2me | Theorems.Thm_HybridOrderAlloc_Thickness_lemma_1_c
-- name    : HybridOrderAlloc.Thickness.lemma_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:16.081993+00:00
-- url     : https://prove2.me/theorems/d3373b49-d2c3-4aa0-b121-468bbf6b8871
-- title:
--   Lemma 1(c), p. 36 — y^U_t ∧ D is an optimal decision of (5), with y^U_t given by (14)
-- statement:
--   Consider the order-allocation dynamic program of He & Goh with value functions $V_t$ given by (5), and let $\partial_1V_{t+1}$ be the right partial derivative of $V_{t+1}$ in $M$.
--
--   For every period $t\in\{1,\dots,T\}$ and every $(M,D)\in\mathbb R^2_{++}$, the set
--   $$\Big\{y\in\mathbb R_+:\ y\ \ge\ (\mu_0-\mu)M+\frac{\gamma\delta M}{2p}\,\mathbb E\big[\partial_1V_{t+1}\big((\rho+\delta R\beta)M+\delta Ry,\ \eta D+\theta M+\epsilon\big)\big]\Big\}$$
--   is nonempty; let $y^U_t(M,D)$ be its infimum (14). Then $y^*_t(M,D)=y^U_t(M,D)\wedge D$ lies in $[0,D]$ and maximizes the objective of (5) over $0\le y\le D$.
--
--   The lemma gives the optimal transfer quantity as a truncation at $D$ of an unconstrained threshold, which is the form used throughout the analysis of the policy.
--
--   **Formalization Note** All statements share the model `Sys` and its standing assumptions `Sys.Standing` (§3). Three kinds of hypotheses are added to the page and disclosed: $r \ge 0$ (Theorem 1 is false for $r<0$); $\rho + \delta R\beta > 0$, $\theta \ge 0$ and $\epsilon \ge 0$ almost surely, which keep the next state of (5) in the domain $M>0$, $D\ge 0$; and $T \ge 1$. Derivatives are right partial derivatives, as in the Notation paragraph of Appendix A.
-- source:
--   He & Goh, Profit or Growth? Dynamic Order Allocation in a Hybrid Workforce, SSRN 3537700 (preprint, 2020-12-25), p. 36, Lemma 1(c), (14)

import Mathlib
import Definitions.Def_HybridOrderAlloc_Thickness_Model

namespace HybridOrderAlloc.Thickness

/-- **Lemma 1(c)**, p. 36: for every period `t ∈ {1, …, T}` and `(M, D) ∈ ℝ²₊₊`, the set in (14)
is nonempty, and `y*_t(M, D) = y^U_t(M, D) ∧ D` is feasible and maximizes the objective of (5)
over `0 ≤ y ≤ D`.
Standing assumptions of §3, with the disclosed additions `r ≥ 0` and `ρ + δRβ > 0`,
`θ ≥ 0`, `ϵ ≥ 0` almost surely (well-posedness of (5)), and `T ≥ 1`. -/
theorem lemma_1_c {Ω : Type*} [MeasurableSpace Ω] (S : Sys Ω) (hS : S.Standing) :
    ∀ t : ℕ, 1 ≤ t → t ≤ S.T → ∀ M D : ℝ, 0 < M → 0 < D →
      (S.yUset t M D).Nonempty ∧ min (S.yU t M D) D ∈ Set.Icc 0 D ∧
        IsMaxOn (S.stage (S.V (t + 1)) M D) (Set.Icc 0 D) (min (S.yU t M D) D) := by sorry

end HybridOrderAlloc.Thickness
