-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_asin_matrix_ge
-- name    : ModernConvex.Relaxations.asin_matrix_ge
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:47.830082+00:00
-- url     : https://prove2.me/theorems/6a39b2ee-130f-44f1-887e-1d1d9285de12
-- title:
--   Nesterov's observation (p. 174): asin[X] ⪰ X for X ⪰ 0 with |Xᵢⱼ| ≤ 1
-- statement:
--   Let $X$ be a symmetric positive semidefinite $n\times n$ real matrix with $|X_{ij}| \le 1$ for all $i, j$, and let $\operatorname{asin}[X]$ be the matrix with the elements $\operatorname{asin}(X_{ij})$. Then
--   $$\operatorname{asin}[X] \succeq X,$$
--   that is, $\operatorname{asin}[X] - X$ is positive semidefinite. In particular this holds for every positive semidefinite $X$ with unit diagonal (for such $X$, $|X_{ij}| \le 1$ automatically).
--
--   Combined with Lemma 4.3.1 and $A \succeq 0$, the observation gives $\operatorname{Tr}(A\operatorname{asin}[X]) \ge \operatorname{Tr}(AX)$ for every feasible $X$ of the relaxation (4.3.18), which completes the proof of Nesterov's $2/\pi$ theorem.
--
--   **Formalization Note** The book states the observation for "a positive semidefinite symmetric matrix $X$ with diagonal entries $\pm1$ (in fact, for any positive semidefinite $X$ with $|X_{ij}| \le 1$)"; the Lean statement is the second, more general form, which contains the first. The observation is unnumbered and cited by its page.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 174, Nesterov's observation (unnumbered, displayed after Lemma 4.3.1)

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open Matrix

namespace ModernConvex.Relaxations

/-- Ben-Tal–Nemirovski, Nesterov's observation, p. 174 (unnumbered): for any positive
semidefinite symmetric matrix `X` with `|Xᵢⱼ| ≤ 1` (in particular for a positive semidefinite
`X` with unit diagonal), `asin[X] ⪰ X`, i.e. `asin[X] − X` is positive semidefinite. -/
theorem asin_matrix_ge {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosSemidef)
    (hX1 : ∀ i j, |X i j| ≤ 1) :
    (asinMatrix X - X).PosSemidef := by sorry

end ModernConvex.Relaxations
