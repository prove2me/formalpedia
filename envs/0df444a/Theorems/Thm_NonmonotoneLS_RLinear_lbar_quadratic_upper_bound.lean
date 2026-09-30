-- Prove2me | Theorems.Thm_NonmonotoneLS_RLinear_lbar_quadratic_upper_bound
-- name    : NonmonotoneLS.RLinear.lbar_quadratic_upper_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T22:31:22.624509+00:00
-- url     : https://prove2.me/theorems/32b240fa-61e4-4832-9e7e-84e69a9fadb6
-- title:
--   Quadratic (descent-lemma) upper bound for $f$ along a trial step $x_k + s\,d_k$ inside $\bar{\mathcal{L}}$
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be $C^1$, let $x_k$, $d_k$ be the iterates and directions of a run, and suppose $\nabla f$ is $L$-Lipschitz on $\bar{\mathcal{L}} = \{x : \operatorname{dist}(x, \mathcal{L}) \le \mu d_{\max}\}$ with $\mathcal{L} = \{y : f(y) \le f(x_0)\}$.
--
--   **Claim.** If $x_k \in \mathcal{L}$ and $0 \le s \le \mu$, then
--
--   $$f(x_k + s\, d_k) \;\le\; f(x_k) + \nabla f(x_k)\, d_k + \tfrac{L}{2} s^2 \|d_k\|^2.$$
--
--   This is the quadratic upper bound (the descent lemma) along the line-search trial step. Every point $x_k + t(s d_k)$, $0 \le t \le 1$, lies in $\bar{\mathcal{L}}$, so Lipschitzness of $\nabla f$ applies on the whole segment; integrating $\|\nabla f(x_k + u d_k) - \nabla f(x_k)\| \le L u \|d_k\|$ along the segment gives the claim.
--
--   The estimate is what turns the failure of the Armijo test at the next trial step $s = \rho\alpha_k$ into a lower bound on $-\nabla f(x_k)\,d_k$, and hence into the $\alpha_k \ge 2(1-\delta)c_1/(L\rho c_2^2)$ step used in Eq. (2.11) of the proof of Theorem 2.1 (p. 1048), with the (3.7) argument applied in the $\bar{\mathcal{L}}$ setting of Theorem 3.1 (p. 1050).
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), Lemma 2.1 and Eq. (2.10)-(2.11) (p. 1048), specialised to the mu*d_max region of Theorem 3.1 (p. 1050)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_RLinear_Run
import Definitions.Def_NonmonotoneLS_RLinear_Regions
import Definitions.Def_NonmonotoneLS_RLinear_Constants
import Theorems.Thm_NonmonotoneLS_RLinear_step_segment_mem_Lbar

open scoped InnerProductSpace NNReal
open Filter

namespace NonmonotoneLS.RLinear

/-- Descent/smoothness estimate on the trial segment: if `x k ∈ 𝓛`, `0 ≤ s ≤ μ` and `∇f` is
`L`-Lipschitz on `𝓛̄`, then `f (x k + s • d k) ≤ f (x k) + s ⟨∇f (x k), d k⟩ + (L/2) s² ‖d k‖²`. -/
theorem lbar_quadratic_upper_bound {n : ℕ} (p : Shared.Params)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ) (s : ℝ)
    (hx : x k ∈ levelSet f (x 0)) (hs0 : 0 ≤ s) (hsμ : s ≤ p.μ)
    (L : ℝ≥0) (hLip : LipschitzOnWith L (gradient f) (Lbar p f x d)) :
    f (x k + s • d k) ≤ f (x k) + s * ⟪gradient f (x k), d k⟫_ℝ
      + (L : ℝ) / 2 * s ^ 2 * ‖d k‖ ^ 2 := by
  sorry

end NonmonotoneLS.RLinear
