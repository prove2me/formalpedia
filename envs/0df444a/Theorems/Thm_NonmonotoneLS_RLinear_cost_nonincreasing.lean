-- Prove2me | Theorems.Thm_NonmonotoneLS_RLinear_cost_nonincreasing
-- name    : NonmonotoneLS.RLinear.cost_nonincreasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:28:02.403353+00:00
-- url     : https://prove2.me/theorems/72e51087-d4af-4a8f-83cb-d3f81e2b90a2
-- title:
--   Proof of Theorem 3.1, first display — $C_{k+1} \le C_k$ and the iterates stay in $\mathcal L$
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be continuously differentiable and consider a run of the Nonmonotone Line Search Algorithm with iterates $x_k$, directions $d_k$ and reference values $C_k$ of (1.6). If $\nabla f(x_k) d_k \le 0$ for each $k$, then for each $k$
--
--   $$f(x_{k+1}) \le C_k \quad\text{and}\quad C_{k+1} \le C_k,$$
--
--   hence $f(x_{k+1}) \le C_k \le \dots \le C_0 = f(x_0)$, and every iterate lies in the level set
--
--   $$\mathcal L = \{x \in \mathbb{R}^n : f(x) \le f(x_0)\}.$$
--
--   This is what confines the whole run to a bounded region when $f$ is strongly convex.
--
--   **Formalization Note.** The paper derives this from $f(x_{k+1}) \le C_k$ and the convex-combination form of $C_{k+1}$; the hypothesis $\nabla f(x_k)d_k \le 0$ is the one under which $f(x_{k+1}) \le C_k$ holds (it follows from (2.4) in Theorem 3.1).
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004), p. 1050, Section 3, proof of Theorem 3.1, first display

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

/-- Section 3, proof of Theorem 3.1, first display (p. 1050): along a run with
`∇f(x_k) d_k ≤ 0` for each `k`, `f(x_{k+1}) ≤ C_k` and `C_{k+1} ≤ C_k` for each `k`, and every
iterate lies in the level set `𝓛 = {y : f(y) ≤ f(x₀)}`. -/
theorem cost_nonincreasing {n : ℕ} (p : Shared.Params) (r : Rule) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : IsNLSARun p r f x d α η)
    (hdesc : ∀ k, ⟪gradient f (x k), d k⟫_ℝ ≤ 0) :
    (∀ k, f (x (k + 1)) ≤ Shared.costC f x η k ∧ Shared.costC f x η (k + 1) ≤ Shared.costC f x η k) ∧
      ∀ k, x k ∈ levelSet f (x 0) := by sorry

end NonmonotoneLS.RLinear
