-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_smooth_compact_dense
-- name    : HunterPDE.Sobolev.smooth_compact_dense
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T07:07:41.722795+00:00
-- url     : https://prove2.me/theorems/78e2b9e8-e5a1-43fa-bc55-861ee508488a
-- title:
--   Theorem 3.24 — C_c^∞(ℝⁿ) is dense in W^{k,p}(ℝⁿ)
-- statement:
--   Let $k \in \mathbb{N}$ (so $k \ge 1$) and $1 \le p < \infty$. Then $C_c^\infty(\mathbb{R}^n)$ is dense in the Sobolev space $W^{k,p}(\mathbb{R}^n)$ of Definition 3.23: for every $f \in W^{k,p}(\mathbb{R}^n)$ and every $\varepsilon > 0$ there is $\varphi \in C_c^\infty(\mathbb{R}^n)$ with
--   $$\|f - \varphi\|_{W^{k,p}(\mathbb{R}^n)} < \varepsilon .$$
--
--   Density lets an inequality proved for test functions (such as Theorem 3.28) be extended to all of $W^{k,p}(\mathbb{R}^n)$, which is how Theorem 3.31 is obtained. It fails for a proper open subset $\Omega$ in place of $\mathbb{R}^n$.
--
--   **Formalization Note.** The norm is `sobolevNorm k p univ` of Definition 3.23, valued in $[0,\infty]$; $\varepsilon$ ranges over positive extended reals, which is equivalent to positive reals. The notes' $\mathbb{N}$ is $\{1, 2, \dots\}$ (they write $\mathbb{N}_0 = \{0, 1, 2, \dots\}$ when $0$ is allowed, §1.8), so the statement assumes $k \ge 1$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 59, Theorem 3.24

import Mathlib
import Definitions.Def_HunterPDE_Sobolev_SobolevSpace

open MeasureTheory

namespace HunterPDE.Sobolev

/-- Theorem 3.24 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 59: for `k ∈ ℕ` and
`1 ≤ p < ∞`, `C_c^∞(ℝⁿ)` is dense in `W^{k,p}(ℝⁿ)`: every `f ∈ W^{k,p}(ℝⁿ)` is approximated in the
norm `‖·‖_{W^{k,p}(ℝⁿ)}` of Definition 3.23 by test functions. The notes' `ℕ` is `{1, 2, …}` (they
write `ℕ₀ = {0, 1, 2, …}` when `0` is allowed, §1.8), hence `1 ≤ k`. -/
theorem smooth_compact_dense {n k : ℕ} (hk : 1 ≤ k) {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW k p Set.univ f)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      IsTestFunction Set.univ φ ∧ sobolevNorm k p Set.univ (f - φ) < ε := by sorry

end HunterPDE.Sobolev
