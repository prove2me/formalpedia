-- Prove2me | Theorems.Thm_HybridOrderAlloc_Thickness_proposition_1
-- name    : HybridOrderAlloc.Thickness.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:00.948605+00:00
-- url     : https://prove2.me/theorems/2ed6cf68-9561-47a7-ba26-0ffca842531c
-- title:
--   Proposition 1, p. 14 — for every period t, V_t(M, D) is jointly concave in (M, D)
-- statement:
--   Consider the order-allocation dynamic program of He & Goh, with value functions $V_t(M,D)$ of market thickness $M$ and firm demand $D$, defined by the Bellman recursion (5) with $V_{T+1}=0$.
--
--   For every period $t\in\{1,\dots,T\}$, the value function is jointly concave on $\mathbb R^2_{++}$:
--   $$V_t\big(\lambda(M,D)+(1-\lambda)(M',D')\big)\ \ge\ \lambda V_t(M,D)+(1-\lambda)V_t(M',D')\qquad\text{for all }(M,D),(M',D')\in\mathbb R^2_{++},\ \lambda\in[0,1].$$
--
--   This is the structural result on which the rest of the analysis rests: it makes the right partial derivatives of $V_t$ monotone and gives the limits of Lemma 2.
--
--   **Formalization Note** All statements share the model `Sys` and its standing assumptions `Sys.Standing` (§3). Three kinds of hypotheses are added to the page and disclosed: $r \ge 0$ (Theorem 1 is false for $r<0$); $\rho + \delta R\beta > 0$, $\theta \ge 0$ and $\epsilon \ge 0$ almost surely, which keep the next state of (5) in the domain $M>0$, $D\ge 0$; and $T \ge 1$. Derivatives are right partial derivatives, as in the Notation paragraph of Appendix A.
-- source:
--   He & Goh, Profit or Growth? Dynamic Order Allocation in a Hybrid Workforce, SSRN 3537700 (preprint, 2020-12-25), p. 14, Proposition 1

import Mathlib
import Definitions.Def_HybridOrderAlloc_Thickness_Model

namespace HybridOrderAlloc.Thickness

/-- **Proposition 1**, p. 14: for every period `t ∈ {1, …, T}`, `V_t(M, D)` is jointly concave in
`(M, D)` on `ℝ²₊₊`.
Standing assumptions of §3, with the disclosed additions `r ≥ 0` and `ρ + δRβ > 0`,
`θ ≥ 0`, `ϵ ≥ 0` almost surely (well-posedness of (5)), and `T ≥ 1`. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (S : Sys Ω) (hS : S.Standing) :
    ∀ t : ℕ, 1 ≤ t → t ≤ S.T →
      ConcaveOn ℝ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) (fun z : ℝ × ℝ => S.V t z.1 z.2) := by sorry

end HybridOrderAlloc.Thickness
