-- Prove2me | Theorems.Thm_KallMayerSLP_KKT_proposition_3_5
-- name    : KallMayerSLP.KKT.proposition_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:19.149879+00:00
-- url     : https://prove2.me/theorems/91c468bd-1e58-4fb1-a7a3-78626a1c5563
-- title:
--   Proposition 3.5 — saddle point theorem: a saddle point solves both the primal and the dual problem
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ and $g_1,\dots,g_m:\mathbb R^n\to\mathbb R$ are convex and continuously differentiable, the book's standing assumptions for the program
--   $$
--   \min f(x)\quad\text{s.t.}\quad g_i(x)\le0,\ i=1,\dots,m,\tag{3.1}
--   $$
--   with feasible set $\mathcal B=\{x\mid g_i(x)\le 0,\ i=1,\dots,m\}$.
--
--   Let $L(x,u)=f(x)+\sum_{i=1}^m u_ig_i(x)$ be the Lagrange function of (3.1), and suppose $(\hat x,\hat u)$ with $\hat u\ge0$ is a saddle point of $L$, i.e. $L(\hat x,u)\le L(\hat x,\hat u)\le L(x,\hat u)$ for all $u\ge 0$ and all $x\in\mathbb R^n$. Then
--   $$
--   \max_{u\ge 0}\ \inf_{x\in\mathbb R^n}L(x,u)\;=\;\min_{x\in\mathbb R^n}\ \sup_{u\ge 0}L(x,u),\tag{3.7}
--   $$
--   and $(\hat x,\hat u)$ solves each of these two problems: $\hat u$ attains the maximum on the left and $\hat x$ attains the minimum on the right.
--
--   The saddle point theorem can be read as a strong duality theorem for nonlinear programming: the left-hand side is the dual problem of (3.1), the right-hand side the primal problem.
--
--   **Formalization Note** Both inner optimizations take values in the extended reals (`EReal`). The conclusion states the equality of the outer supremum and infimum, that $\hat u$ maximizes the dual function over $u\ge0$, that $\hat x$ minimizes the primal function over $\mathbb R^n$, and that the two attained values coincide.
--
--   Differences from the source:
--   - encoding: ℝⁿ with zᵀv → EuclideanSpace ℝ (Fin n) with the inner product ⟪z, v⟫ and Mathlib's gradient; reason: Lean convention; the same space and the same gradient for differentiable functions
--   - encoding: max_{u≥0} inf_x L and min_x sup_{u≥0} L, attained at û and x̂ → EReal-valued dual/primal functions; ⨆_{u≥0} = ⨅_x, IsMaxOn at û, IsMinOn at x̂, equal values; reason: the inner inf and sup may be ∓∞; max/min are a supremum/infimum together with attainment
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3.1, Proposition 3.5, eq. (3.7), p.66 (PDF 77)

import Mathlib
import Definitions.Def_KallMayerSLP_KKT_IsSaddlePoint
import Definitions.Def_KallMayerSLP_KKT_dualFunction
import Definitions.Def_KallMayerSLP_KKT_primalFunction

namespace KallMayerSLP.KKT

/-- **Proposition 3.5 (saddle point theorem).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3.1, Proposition 3.5, p.66 (PDF 77): "If for the Lagrange function to (3.1) there exists a
saddle point `(x̂, û ≥ 0)`, then
`max_{u≥0} inf_{x∈ℝⁿ} L(x, u) = min_{x∈ℝⁿ} sup_{u≥0} L(x, u)`, (3.7)
and `(x̂, û)` solves each of these two problems."

Here `f` and every `gᵢ` are convex on `ℝⁿ` and continuously differentiable (`ContDiff ℝ 1`), the
book's standing assumptions for (3.1) (p.61 and p.62), and `(x̂, û)` is a saddle point in the sense of (3.6).

**Formalization Note.** `inf_x L(x, u)` (`dualFunction`) and `sup_{u≥0} L(x, u)`
(`primalFunction`) take values in `EReal`. The conclusion has four conjuncts: the supremum over
`u ≥ 0` of the dual function equals the infimum over `x` of the primal function; `û` maximizes the
dual function over `u ≥ 0` and `x̂` minimizes the primal function over `ℝⁿ` (so the `max` and the
`min` of (3.7) are attained, at `û` and `x̂`); and the two attained values coincide. -/
theorem proposition_3_5 {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hf1 : ContDiff ℝ 1 f) (hg1 : ∀ i, ContDiff ℝ 1 (g i))
    (xh : EuclideanSpace ℝ (Fin n)) (uh : Fin m → ℝ) (h : IsSaddlePoint f g xh uh) :
    ((⨆ (u : Fin m → ℝ) (_ : 0 ≤ u), dualFunction f g u) = ⨅ x, primalFunction f g x) ∧
    IsMaxOn (dualFunction f g) {u | 0 ≤ u} uh ∧
    IsMinOn (primalFunction f g) Set.univ xh ∧
    dualFunction f g uh = primalFunction f g xh := by sorry

end KallMayerSLP.KKT
