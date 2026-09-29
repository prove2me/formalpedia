-- Prove2me | Theorems.Thm_NonmonotoneLS_RLinear_sufficient_decrease
-- name    : NonmonotoneLS.RLinear.sufficient_decrease
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:36:20.422649+00:00
-- url     : https://prove2.me/theorems/3e187aec-4f44-44bd-9538-324ba73c0750
-- title:
--   Eq. (3.6) — $f(x_{k+1}) \le C_k - \beta\|g_k\|^2$ with $\beta$ of (2.9)
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable and consider a run of the Nonmonotone Line Search Algorithm (Wolfe or Armijo rule) with iterates $x_k$, directions $d_k$, steps $\alpha_k$ and reference values $C_k$; write $g_k = \nabla f(x_k)$. Assume
--
--   1. there are $c_1, c_2 > 0$ with $g_k^{\mathsf T} d_k \le -c_1\|g_k\|^2$ and $\|d_k\| \le c_2\|g_k\|$ for every $k$;
--   2. $\alpha_k \le \mu$ for every $k$;
--   3. $\nabla f$ is Lipschitz continuous with constant $L > 0$ on $\bar{\mathcal L}$, the set of points whose distance to $\mathcal L = \{x : f(x) \le f(x_0)\}$ is at most $\mu d_{\max}$, $d_{\max} = \sup_k \|d_k\|$.
--
--   Then for every $k$
--
--   $$f(x_{k+1}) \le C_k - \beta \|g_k\|^2, \quad (3.6)$$
--
--   where
--
--   $$\beta = \min\left\{\frac{\delta\mu c_1}{\rho},\ \frac{2\delta(1-\delta)c_1^2}{L\rho c_2^2},\ \frac{\delta(1-\sigma)c_1^2}{L c_2^2}\right\}. \quad (2.9)$$
--
--   This is the sufficient-decrease inequality that drives both the global convergence proof and the linear rate.
--
--   **Formalization Note.** The paper cites (3.6) from the proof of Theorem 2.2, where it is (2.8). Here the direction assumption is required at every $k$, as in Theorem 3.1, and one Lipschitz constant on $\bar{\mathcal L}$ serves both rules (for the Wolfe rule the proof only needs it on $\mathcal L \subseteq \bar{\mathcal L}$). $L > 0$ is assumed because $L$ divides in $\beta$; a Lipschitz constant can always be enlarged. $d_{\max}$ is computed in $[0, \infty]$.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1050, Eq. (3.6), with beta from p. 1047, Eq. (2.9)

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

/-- Eq. (3.6) (p. 1050), i.e. (2.8) with `β` of (2.9): along a run whose directions satisfy
(2.4)–(2.5) with constants `c₁, c₂ > 0` at every `k`, whose steps satisfy `α_k ≤ μ`, and for which
`∇f` is `L`-Lipschitz (`L > 0`) on `𝓛̄`, `f(x_{k+1}) ≤ C_k - β ‖∇f(x_k)‖²` for every `k`. -/
theorem sufficient_decrease {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hdir : DirectionBounds f x d c₁ c₂)
    (hαμ : ∀ k, α k ≤ p.μ)
    (L : ℝ≥0) (hL : 0 < L) (hLip : LipschitzOnWith L (gradient f) (Lbar p f x d)) :
    ∀ k, f (x (k + 1)) ≤ Shared.costC f x η k - beta p c₁ c₂ L * ‖gradient f (x k)‖ ^ 2 := by sorry

end NonmonotoneLS.RLinear
