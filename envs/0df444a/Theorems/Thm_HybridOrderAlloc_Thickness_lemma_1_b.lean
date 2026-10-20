-- Prove2me | Theorems.Thm_HybridOrderAlloc_Thickness_lemma_1_b
-- name    : HybridOrderAlloc.Thickness.lemma_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:14.527517+00:00
-- url     : https://prove2.me/theorems/3bc9cf37-1cd1-465f-85de-c6bb9d0fc599
-- title:
--   Lemma 1(b), p. 35 — the right partial derivatives ∂₁V_t, ∂₂V_t are uniformly bounded on ℝ²₊₊
-- statement:
--   Consider the order-allocation dynamic program of He & Goh and the right partial derivatives $\partial_1V_t$, $\partial_2V_t$ of the value function in $M$ and in $D$.
--
--   For every period $t\in\{1,\dots,T\}$ there is a constant $\Gamma_t$ such that
--   $$|\partial_1V_t(M,D)|\le\Gamma_t\quad\text{and}\quad|\partial_2V_t(M,D)|\le\Gamma_t\qquad\text{for all }(M,D)\in\mathbb R^2_{++}.$$
--
--   Uniform boundedness justifies exchanging derivatives, limits and expectations in the later lemmas.
--
--   **Formalization Note** All statements share the model `Sys` and its standing assumptions `Sys.Standing` (§3). Three kinds of hypotheses are added to the page and disclosed: $r \ge 0$ (Theorem 1 is false for $r<0$); $\rho + \delta R\beta > 0$, $\theta \ge 0$ and $\epsilon \ge 0$ almost surely, which keep the next state of (5) in the domain $M>0$, $D\ge 0$; and $T \ge 1$. Derivatives are right partial derivatives, as in the Notation paragraph of Appendix A.
-- source:
--   He & Goh, Profit or Growth? Dynamic Order Allocation in a Hybrid Workforce, SSRN 3537700 (preprint, 2020-12-25), p. 35, Lemma 1(b)

import Mathlib
import Definitions.Def_HybridOrderAlloc_Thickness_Model

namespace HybridOrderAlloc.Thickness

/-- **Lemma 1(b)**, p. 35: for every period `t ∈ {1, …, T}`, the right partial derivatives
`∂₁V_t`, `∂₂V_t` are uniformly bounded on `ℝ²₊₊` (the bound may depend on `t`).
Standing assumptions of §3, with the disclosed additions `r ≥ 0` and `ρ + δRβ > 0`,
`θ ≥ 0`, `ϵ ≥ 0` almost surely (well-posedness of (5)), and `T ≥ 1`. -/
theorem lemma_1_b {Ω : Type*} [MeasurableSpace Ω] (S : Sys Ω) (hS : S.Standing) :
    ∀ t : ℕ, 1 ≤ t → t ≤ S.T → ∃ Γ : ℝ, ∀ M D : ℝ, 0 < M → 0 < D →
      |S.d1V t M D| ≤ Γ ∧ |S.d2V t M D| ≤ Γ := by sorry

end HybridOrderAlloc.Thickness
