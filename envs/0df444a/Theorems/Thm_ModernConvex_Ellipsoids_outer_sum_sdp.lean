-- Prove2me | Theorems.Thm_ModernConvex_Ellipsoids_outer_sum_sdp
-- name    : ModernConvex.Ellipsoids.outer_sum_sdp
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:53.424662+00:00
-- url     : https://prove2.me/theorems/7285c5fb-db52-462b-a9b4-642d8aa73441
-- title:
--   Proposition 4.9.4 — every feasible solution of (Õ) with t > 0 gives W[Z] ⊇ W₁ + ⋯ + W_m of volume ≤ t^{−n/2}
-- statement:
--   Let $W_i=\{x\in\mathbb R^n \mid x^TB_ix\le1\}$ with $B_i\succ0$, $i=1,\dots,m$, be full-dimensional ellipsoids centred at the origin. Let $B^i$ and $M[Z]$ be the $(mn)\times(mn)$ block matrices defined above. Consider the semidefinite program
--   $$\max_{t,Z,\lambda}\Big\{t \;\Big|\; t\le\operatorname{Det}^{1/n}(Z),\ \sum_{i=1}^m\lambda_iB^i\succeq M[Z],\ \lambda_i\ge0,\ Z\succeq0,\ \sum_{i=1}^m\lambda_i=1\Big\}.\qquad(\tilde O)$$
--
--   1. Every feasible solution $(t,Z,\lambda)$ of $(\tilde O)$ with $t>0$ has $Z\succ0$. The ellipsoid $W[Z]=\{x \mid x^TZx\le1\}$ then contains $W_1+\dots+W_m$, and its normalized volume satisfies
--   $$\operatorname{Vol}(W[Z])\le t^{-n/2}.$$
--   2. The smallest-volume ellipsoid obtained this way comes from any optimal solution. If $(t_*,Z_*,\lambda_*)$ is optimal for $(\tilde O)$ and $(t,Z,\lambda)$ is feasible with $t>0$, then $\operatorname{Vol}(W[Z_*])\le\operatorname{Vol}(W[Z])$.
--
--   **Formalization Note** Volume is normalized: Lebesgue measure divided by the measure of the unit Euclidean ball, valued in $[0,\infty]$, with $t^{-n/2}$ embedded as a nonnegative extended real. $\operatorname{Det}^{1/n}$ and $t^{-n/2}$ are real powers. "Optimal" means feasible with no feasible triple having larger $t$; existence of an optimal solution is not asserted. "Produces ellipsoid" is rendered as $Z\succ0$ (`PosDef`), which makes $W[Z]$ a full-dimensional ellipsoid.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 267–268, Proposition 4.9.4

import Mathlib
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
import Definitions.Def_ModernConvex_Ellipsoids_Programs

open Matrix

namespace ModernConvex.Ellipsoids

/-- Ben-Tal–Nemirovski, Proposition 4.9.4, pp. 267–268. Given `m` centred at the origin
full-dimensional ellipsoids `Wᵢ = {x ∈ ℝⁿ | xᵀBᵢx ≤ 1}`, `Bᵢ ≻ 0`, consider the semidefinite
program (Õ): `max_{t,Z,λ} { t | t ≤ Det^{1/n}(Z), Σᵢ λᵢBⁱ ⪰ M[Z], λᵢ ≥ 0, Z ⪰ 0, Σᵢ λᵢ = 1 }`.
Every feasible solution `(t, Z, λ)` with positive value of the objective produces the
(full-dimensional, `Z ≻ 0`) ellipsoid `W[Z] = {x | xᵀZx ≤ 1}`, which contains `W₁ + ⋯ + W_m` and
has (normalized) volume at most `t^{−n/2}`. The smallest-volume ellipsoid obtained in this way is
given by any optimal solution of (Õ). -/
theorem outer_sum_sdp {m n : ℕ} (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ i, (B i).PosDef) :
    (∀ (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) (lam : Fin m → ℝ), OFeasible B t Z lam → 0 < t →
      Z.PosDef ∧ minkowskiSum (fun i => quadSet (B i)) ⊆ quadSet Z ∧
        Vol (quadSet Z) ≤ ENNReal.ofReal (t ^ (-(n : ℝ) / 2))) ∧
    (∀ (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) (lam : Fin m → ℝ), OOptimal B t Z lam →
      ∀ (t' : ℝ) (Z' : Matrix (Fin n) (Fin n) ℝ) (lam' : Fin m → ℝ), OFeasible B t' Z' lam' →
        0 < t' → Vol (quadSet Z) ≤ Vol (quadSet Z')) := by sorry

end ModernConvex.Ellipsoids
