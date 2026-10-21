-- Prove2me | Theorems.Thm_MaxValSens_Wolfe_theorem_3_3_multiplier_limit
-- name    : MaxValSens.Wolfe.theorem_3_3_multiplier_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:36.484875+00:00
-- url     : https://prove2.me/theorems/400cf95d-445f-48c5-8647-088efdd5914a
-- title:
--   Proof of Theorem 3.3 (ii), p. 18 — multipliers λᵏ ∈ Σ(xᵏ, yᵏ) converge to some λ̃ ∈ Σ(x̄, ỹ) under a stable parametric CQ
-- statement:
--   Assume the standing assumption of §3.2 at $\bar x$. Let $\tilde y\in\mathcal S(\bar x)$ and suppose a stable parametric CQ holds for $(P_{\bar x})$ at $\tilde y$. Let $x^k\to\bar x$ and $y^k\to\tilde y$ with $y^k\in\mathcal S(x^k)$ for all $k$. Then, along a subsequence $k_j$, there are multipliers $\lambda^j\in\Sigma(x^{k_j},y^{k_j})$ and $\tilde\lambda$ with
--
--   $$\lambda^j\to\tilde\lambda\qquad\text{and}\qquad\tilde\lambda\in\Sigma(\bar x,\tilde y).$$
--
--   This supplies the converging primal–dual pairs $(x^k,y^k,\lambda^k)\to(\bar x,\tilde y,\tilde\lambda)$ at which (3.12) is applied in the proof of (3.13)–(3.14).
--
--   **Formalization Note** The stable parametric CQ is `StableParamCQ` (Definition 2.3 with (i) read for local maximizers on a neighbourhood of $(\bar x,\tilde y)$). $\Sigma=\Sigma^1$ is `SigmaM 1`.
-- source:
--   Guo, Ye, Zhang, Sensitivity analysis of the maximal value function with applications in nonconvex minimax programs, arXiv:2303.01474v1, p. 18, proof of Theorem 3.3 (ii)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_MaxValSens_Wolfe_Setting
open Filter Topology
open scoped InnerProductSpace

namespace MaxValSens.Wolfe

/-- Proof of Theorem 3.3 (ii), p. 18: if a stable parametric CQ holds for `(P_x̄)` at
`ỹ ∈ S(x̄)`, `xₖ → x̄`, `yₖ → ỹ` and `yₖ ∈ S(xₖ)`, then along a subsequence there are
multipliers `λₖ ∈ Σ(xₖ, yₖ)` converging to some `λ̃ ∈ Σ(x̄, ỹ)`. -/
theorem theorem_3_3_multiplier_limit {n m q : ℕ} (f : E n → E m → ℝ)
    (g : Fin q → E n → E m → ℝ) (xbar : E n) (ytil : E m)
    (hS : Standing f g xbar) (hytil : ytil ∈ S f g xbar) (hPCQ : StableParamCQ f g xbar ytil)
    (xs : ℕ → E n) (ys : ℕ → E m) (hx : Tendsto xs atTop (𝓝 xbar))
    (hy : Tendsto ys atTop (𝓝 ytil)) (hys : ∀ k, ys k ∈ S f g (xs k)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ lams : ℕ → Fin q → ℝ,
      (∀ k, lams k ∈ SigmaM 1 f g (xs (φ k)) (ys (φ k))) ∧
      ∃ lamtil ∈ SigmaM 1 f g xbar ytil, Tendsto lams atTop (𝓝 lamtil) := by sorry

end MaxValSens.Wolfe
