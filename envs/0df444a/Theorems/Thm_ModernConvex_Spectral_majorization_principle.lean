-- Prove2me | Theorems.Thm_ModernConvex_Spectral_majorization_principle
-- name    : ModernConvex.Spectral.majorization_principle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:39.435403+00:00
-- url     : https://prove2.me/theorems/09334e4e-60b2-4847-9e47-653ee5c5d8af
-- title:
--   Claim (majorization principle) — the permutation hull X[x] is cut out by (+)
-- statement:
--   For $x \in \mathbb R^m$ let $X[x]$ be the set of all convex combinations of the $m!$ vectors obtained from $x$ by permuting its coordinates. For $y \in \mathbb R^m$ and $1 \le j \le m$ let $S_j(y)$ be the sum of the $j$ largest entries of $y$. Then $X[x]$ is exactly the solution set of the system
--   $$S_j(y) \le S_j(x),\quad j = 1,\dots,m-1, \qquad y_1 + \cdots + y_m = x_1 + \cdots + x_m \tag{+}$$
--   in the variables $y \in \mathbb R^m$.
--
--   The inclusion of $X[x]$ in the solution set is Exercise 4.14 and the reverse inclusion is Exercise 4.15. Exercise 4.16 uses the principle to prove Proposition 4.2.1. It is the classical characterization of majorization (Hardy–Littlewood–Pólya, Rado).
--
--   **Formalization Note** For $m \le 1$ the family of inequalities is empty and only the sum equation remains.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 285, Claim (majorization principle), system (+); Exercises 4.14–4.15

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR

open Matrix

namespace ModernConvex.Spectral

/-- Ben-Tal–Nemirovski, Claim (majorization principle), p. 285 (Exercises 4.14–4.15): for
`x ∈ ℝᵐ`, the convex hull `X[x]` of the permutations of `x` is exactly the solution set of the
system (+) in `y ∈ ℝᵐ`: `Sⱼ(y) ≤ Sⱼ(x)` for `j = 1, …, m − 1`, and `y₁ + ⋯ + y_m = x₁ + ⋯ + x_m`,
where `Sⱼ(y)` is the sum of the `j` largest entries of `y`. -/
theorem majorization_principle {m : ℕ} (x : Fin m → ℝ) :
    permHull x =
      {y : Fin m → ℝ | (∀ j : ℕ, 1 ≤ j → j ≤ m - 1 → sumLargest j y ≤ sumLargest j x) ∧
        ∑ i, y i = ∑ i, x i} := by sorry

end ModernConvex.Spectral
