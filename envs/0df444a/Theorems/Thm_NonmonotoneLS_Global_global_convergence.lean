-- Prove2me | Theorems.Thm_NonmonotoneLS_Global_global_convergence
-- name    : NonmonotoneLS.Global.global_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:30:46.622068+00:00
-- url     : https://prove2.me/theorems/167438ac-7cc8-4d34-b731-695d1879c58d
-- title:
--   Theorem 2.2 — global convergence of the nonmonotone line search algorithm
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable and bounded from below, fix NLSA parameters $0 \le \eta_{\min} \le \eta_{\max} \le 1$, $0 < \delta < \sigma < 1 < \rho$, $\mu > 0$, and let $(x_k, d_k, \alpha_k, \eta_k)$ be a run of the nonmonotone line search algorithm with the Wolfe rule or with the Armijo rule. Suppose
--
--   1. $\nabla f(x_k) d_k \le 0$ for every $k$;
--   2. the direction assumption (2.4)–(2.5) holds: for some $c_1, c_2 > 0$, $\nabla f(x_k) d_k \le -c_1\|\nabla f(x_k)\|^2$ and $\|d_k\| \le c_2\|\nabla f(x_k)\|$ for all sufficiently large $k$;
--   3. for some $L$, $\nabla f$ is $L$-Lipschitz on the level set $\mathcal L = \{x : f(x) \le f(x_0)\}$ if the Wolfe conditions are used, and on $\bar{\mathcal L}$, the set of points at distance at most $\mu d_{\max}$ from $\mathcal L$ with $d_{\max} = \sup_k\|d_k\|$, if the Armijo conditions are used.
--
--   Then
--
--   $$\liminf_{k\to\infty} \|\nabla f(x_k)\| = 0. \qquad (2.6)$$
--
--   Moreover, if $\eta_{\max} < 1$, then
--
--   $$\lim_{k\to\infty} \nabla f(x_k) = 0, \qquad (2.7)$$
--
--   and hence every limit point $x^*$ of a convergent subsequence of the iterates satisfies $\nabla f(x^*) = 0$.
--
--   This is the global convergence theorem for the averaged nonmonotone line search: it holds for nonconvex $f$ and for every choice of the weights $\eta_k$, the case $\eta_k \equiv 0$ being the classical monotone line search.
--
--   **Formalization Note.** (a) Hypothesis 1 is not in the printed theorem. The proof needs $f(x_{k+1}) \le C_k$ at every $k$, both to keep every iterate in $\mathcal L$ (where the Wolfe case assumes the Lipschitz condition) and to bound $C_k$ below by $f(x_k)$; that is the hypothesis of Lemma 1.1, which the algorithm's line search presupposes. Without it an early ascent step could leave $\mathcal L$. The direction assumption itself stays "for all sufficiently large $k$", as printed. (b) (2.6) is stated as "for every $\varepsilon > 0$, $\|\nabla f(x_k)\| < \varepsilon$ for infinitely many $k$", equivalent for a nonnegative sequence; Lean's real $\liminf$ would return $0$ for a divergent sequence. (c) The final "Hence" sentence is derived from (2.7), so it is stated under $\eta_{\max} < 1$. (d) $d_{\max}$ and distances are taken in $[0,\infty]$, so an unbounded direction sequence gives $\bar{\mathcal L} = \mathbb{R}^n$. (e) The Lipschitz condition is assumed only on the set the theorem names, never globally.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1047, Theorem 2.2

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Theorem 2.2 (p. 1047). Let `f` be continuously differentiable and bounded from below, and let
`(x_k, d_k, α_k, η_k)` be a run of the NLSA with `∇f(x_k) d_k ≤ 0` for every `k`, satisfying the
direction assumption (2.4)–(2.5), where `∇f` is Lipschitz on `𝓛` if the Wolfe conditions are used
and on `𝓛̄` if the Armijo conditions are used. Then
(2.6) `liminf_k ‖∇f(x_k)‖ = 0` (stated as: for every `ε > 0`, `‖∇f(x_k)‖ < ε` for infinitely
many `k`); and if `η_max < 1`, (2.7) `∇f(x_k) → 0` and every limit of a convergent subsequence
of `(x_k)` is a stationary point. -/
theorem global_convergence {n : ℕ} (p : Shared.Params) (r : Rule)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : BddBelow (Set.range f))
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0)
    (hdir : DirectionAssumption f x d)
    (hLip : ∃ L : ℝ≥0, LipschitzHyp p r f x d L) :
    (∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ‖gradient f (x k)‖ < ε) ∧
      (p.ηmax < 1 → Tendsto (fun k => gradient f (x k)) atTop (𝓝 0)) ∧
      (p.ηmax < 1 → ∀ xstar : EuclideanSpace ℝ (Fin n),
        (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 xstar)) →
          gradient f xstar = 0) := by sorry

end NonmonotoneLS.Global
