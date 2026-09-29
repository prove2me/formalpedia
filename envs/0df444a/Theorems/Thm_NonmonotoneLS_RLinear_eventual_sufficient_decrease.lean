-- Prove2me | Theorems.Thm_NonmonotoneLS_RLinear_eventual_sufficient_decrease
-- name    : NonmonotoneLS.RLinear.eventual_sufficient_decrease
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:51:08.629999+00:00
-- url     : https://prove2.me/theorems/6d503eed-5e79-4498-bf18-dd5ab661dd39
-- title:
--   Theorem 3.2 — R-linearly convergent iterates eventually satisfy the nonmonotone condition (1.4)
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable and let $x^*$ be a minimizer of $f$. Let $x_k$, $d_k$, $\alpha_k$ ($k = 0, 1, \dots$) be any sequences with $x_{k+1} = x_k + \alpha_k d_k$ (not necessarily a run of the algorithm), and write $g_k = \nabla f(x_k)$. Assume:
--
--   1. $f(x_k)$ converges R-linearly to $f(x^*)$: there are $\theta \in (0, 1)$ and $c$ with $f(x_k) - f(x^*) \le c\,\theta^k$ for all $k$;
--   2. the $x_k$ lie in a closed, bounded, convex set $K$ on which $f$ satisfies (3.1) with a constant $\gamma > 0$ (for all $x, y \in K$) and $\nabla f$ is Lipschitz continuous with constant $L$;
--   3. the direction assumption holds: there are $c_1, c_2 > 0$ with $g_k^{\mathsf T} d_k \le -c_1\|g_k\|^2$ and $\|d_k\| \le c_2\|g_k\|$ for all sufficiently large $k$;
--   4. $0 < \alpha_k \le \mu$ for all $k$;
--   5. $C_k$ is given by the recursion (1.6) with weights $\eta_k \in [\eta_{\min}, \eta_{\max}]$, $0 \le \eta_{\min} \le \eta_{\max} \le 1$, and $\eta_{\min} > \theta$.
--
--   Then for every $\delta \in (0, 1)$, condition (1.4),
--
--   $$f(x_k + \alpha_k d_k) \le C_k + \delta \alpha_k g_k^{\mathsf T} d_k,$$
--
--   holds for all sufficiently large $k$.
--
--   So with averaging weights close enough to 1, the sufficient-decrease test (1.4) of the nonmonotone line search is eventually passed by the steps of any R-linearly convergent descent method of this kind.
--
--   **Formalization Note.** The statement follows the page. $\delta$ is the parameter of (1.4), arbitrary in $(0,1)$. The printed proof applies (3.1) and the Lipschitz bound with $y = x^*$, which need not lie in $K$; a cluster point of the $x_k$ in the compact set $K$ is also a minimizer and can take its place, so the statement is unaffected. The proof's limit $\Phi$ of $\varphi_k$ can likewise be replaced by a positive lower bound $\varphi_{k_0}$. If $c \le 0$ the hypothesis forces $f(x_k) = f(x^*)$ for all $k$.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1051, Theorem 3.2

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_RLinear_Run
import Definitions.Def_NonmonotoneLS_RLinear_Regions
import Definitions.Def_NonmonotoneLS_RLinear_Constants

open scoped InnerProductSpace NNReal
open Filter

namespace NonmonotoneLS.RLinear

/-- Theorem 3.2 (p. 1051): let `x*` minimize `f` and let `x_{k+1} = x_k + α_k d_k` be any sequence
with `f(x_k) - f(x*) ≤ cθ^k`, `θ ∈ (0, 1)`, lying in a closed, bounded, convex set `K` on which
(3.1) holds with constant `γ` and `∇f` is `L`-Lipschitz, whose directions satisfy (2.4)–(2.5) for
all sufficiently large `k`, and whose steps satisfy `0 < α_k ≤ μ`. If `C_k` is given by (1.6) with
`η_k ∈ [η_min, η_max] ⊆ [0, 1]` and `η_min > θ`, then for every `δ ∈ (0, 1)` the condition (1.4),
`f(x_k + α_k d_k) ≤ C_k + δ α_k ∇f(x_k) d_k`, holds for all sufficiently large `k`. -/
theorem eventual_sufficient_decrease {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hupd : ∀ k, x (k + 1) = x k + α k • d k)
    (θ c : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hRlin : ∀ k, f (x k) - f xstar ≤ c * θ ^ k)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKc : IsClosed K) (hKb : Bornology.IsBounded K)
    (hKconv : Convex ℝ K) (hxK : ∀ k, x k ∈ K)
    (γ : ℝ) (hγ : 0 < γ)
    (hscK : ∀ u ∈ K, ∀ v ∈ K,
      f v + ⟪gradient f v, u - v⟫_ℝ + 1 / (2 * γ) * ‖u - v‖ ^ 2 ≤ f u)
    (L : ℝ≥0) (hLip : LipschitzOnWith L (gradient f) K)
    (hdir : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ k in atTop,
      ⟪gradient f (x k), d k⟫_ℝ ≤ -c₁ * ‖gradient f (x k)‖ ^ 2 ∧
        ‖d k‖ ≤ c₂ * ‖gradient f (x k)‖)
    (μ : ℝ) (hα : ∀ k, 0 < α k ∧ α k ≤ μ)
    (ηmin ηmax : ℝ) (hηmin0 : 0 ≤ ηmin) (hηle : ηmin ≤ ηmax) (hηmax1 : ηmax ≤ 1)
    (hη : ∀ k, η k ∈ Set.Icc ηmin ηmax) (hθη : θ < ηmin)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ k in atTop,
      f (x k + α k • d k) ≤ Shared.costC f x η k + δ * α k * ⟪gradient f (x k), d k⟫_ℝ := by sorry

end NonmonotoneLS.RLinear
