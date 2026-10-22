-- Prove2me | Theorems.Thm_ModernConvex_Truss_observation_O
-- name    : ModernConvex.Truss.observation_O
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:32.346523+00:00
-- url     : https://prove2.me/theorems/99342e5b-3215-4968-8360-22ac8ea3f7c0
-- title:
--   (O) — the energy inequality has no solution iff its conic quadratic form (3.4.48) has none
-- statement:
--   Let $(n, m, B_1, \dots, B_n)$ be a ground structure ($B_i$ an $m \times k_i$ real matrix), $t \in \mathbb R^n$ with $t \ge 0$, $f \in \mathbb R^m$, $\tau \in \mathbb R$, $A(t) = \sum_i t_iB_iB_i^T$, and
--   $$B(t) = \sqrt2\begin{pmatrix}\sqrt{t_1}B_1^T \\ \sqrt{t_2}B_2^T \\ \vdots \\ \sqrt{t_n}B_n^T\end{pmatrix}. \qquad (3.4.46)$$
--   The inequality $Q(v) := \tfrac12 v^TA(t)v - f^Tv + \tau \le 0$ (3.4.45) has no solution $v \in \mathbb R^m$ if and only if the conic quadratic inequality in $v$
--   $$\left\|\begin{pmatrix} B(t)v \\ 1 - f^Tv + \tau\end{pmatrix}\right\|_2 \le 1 + f^Tv - \tau \qquad (3.4.48)$$
--   has no solution.
--
--   This is the step that turns the description of the strict epigraph of the compliance by a convex quadratic inequality into a statement about a conic quadratic inequality.
--
--   **Formalization Note** The rows of $B(t)$ are indexed by the pairs $(i, j)$ with $j \le k_i$; the Euclidean norm is the square root of the sum of squares of all entries of $B(t)v$ and of $1 - f^Tv + \tau$. The hypothesis $t \ge 0$ is the section's (trusses are nonnegative), and keeps $\sqrt{t_i}$ meaningful.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 124, statement (O)

import Mathlib
import Definitions.Def_ModernConvex_Truss_Compliance

open Matrix

namespace ModernConvex.Truss

/-- Ben-Tal–Nemirovski, observation (O), p. 124. Let `t ≥ 0`, `f ∈ ℝᵐ`, `τ ∈ ℝ`, and
`Q(v) = ½ vᵀA(t)v − fᵀv + τ`. Inequality (3.4.45), `Q(v) ≤ 0`, has no solutions iff the conic
quadratic inequality in `v`
`‖(B(t)v; 1 − fᵀv + τ)‖₂ ≤ 1 + fᵀv − τ` (3.4.48)
has no solution, where `B(t) = √2 [√t₁B₁ᵀ; …; √tₙBₙᵀ]` (3.4.46). -/
theorem observation_O {n m : ℕ} {k : Fin n → ℕ}
    (B : (i : Fin n) → Matrix (Fin m) (Fin (k i)) ℝ) (t : Fin n → ℝ) (ht : 0 ≤ t)
    (f : Fin m → ℝ) (τ : ℝ) :
    (¬ ∃ v : Fin m → ℝ, (1 / 2 : ℝ) * (v ⬝ᵥ (stiffness B t *ᵥ v)) - f ⬝ᵥ v + τ ≤ 0) ↔
    (¬ ∃ v : Fin m → ℝ,
      Real.sqrt (∑ r, (stackedMatrix B t *ᵥ v) r ^ 2 + (1 - f ⬝ᵥ v + τ) ^ 2) ≤ 1 + f ⬝ᵥ v - τ) := by sorry

end ModernConvex.Truss
